from util import *
import axiom

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = self.of(Sum)
    variables = self.variables

    for _, cond in function.of(Piecewise):
        assert not cond.has(*variables)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in function.of(Piecewise)]

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)

    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)
    D = Symbol.D(etype=dtype.integer, given=True)

    f = Function.f(real=True)
    h = Function.h(real=True)

    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Contains(x, A) & Contains(y, B)), (h(i, j), True))))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(algebra.et.given.et.subs.bool, index=Slice[:2])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0, invert=True)


if __name__ == '__main__':
    run()

