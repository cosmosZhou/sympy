from util import *


@apply
def apply(self):
    function, *limits = self.of(Sum)
    assert len(limits) >= 2

    index = 0

    while True:
        index += 1
        _limits = self.limits[:index]
        _vars = [j for j, *_ in _limits]
        if all(not cond.has(*_vars) for expr, cond in function.of(Piecewise)):
            limits = _limits
            vars = _vars
            continue
        else:
            index -= 1
            break

    i_limit = self.limits[index:]
    assert not any(limit.has(*vars) for limit in i_limit)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in function.of(Piecewise)]

    return Equal(self, self.func(Piecewise(*ecs), *i_limit).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)
    D = Symbol.D(etype=dtype.integer)

    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)

    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Contains(i, A)), (g(i, j), Contains(i, B)), (h(i, j), True))))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.expr.args[0].expr.apply(algebra.sum.bool)
    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(algebra.sum.bool)
    Eq << Eq[-1].this.rhs.expr.args[2].expr.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.lhs.expr.args[0].expr.args[1].apply(algebra.bool.to.mul)
    Eq << Eq[-1].this.lhs.expr.args[1].expr.args[1].apply(algebra.bool.to.mul)
    Eq << Eq[-1].this.lhs.expr.args[2].expr.args[1].apply(algebra.bool.to.mul)

    Eq << Sum(Eq[-1].lhs.expr, Eq[-1].lhs.limits[0]).this.apply(algebra.sum.to.piecewise)

    Eq << Eq[-2].this.rhs.expr.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()

