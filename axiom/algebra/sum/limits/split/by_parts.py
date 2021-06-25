from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self, index=-1):
    function, *limits = self.of(Sum)
    assert len(limits) >= 2
    i_limit = self.limits[index:]
    limits = self.limits[:index]

    j = [j for j, *_ in limits]

    assert not any(limit.has(*j) for limit in i_limit)

    return Equal(self, self.func(self.func(function, *limits).simplify(), *i_limit).simplify(), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    C = Symbol.C(etype=dtype.integer)
    D = Symbol.D(etype=dtype.integer)

    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)

    Eq << apply(Sum[j, i:C](Piecewise((f(i, j), Equal(j, a)), (g(i, j), Equal(j, b)), (0, True))))

    Eq << Sum[j](Eq[0].lhs.function).this.simplify()

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, C))


if __name__ == '__main__':
    run()

