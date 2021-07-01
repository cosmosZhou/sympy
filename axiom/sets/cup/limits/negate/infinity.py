from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, calculus

    i = Symbol.i(integer=True)
    f = Function.f(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    n = Symbol.n(integer=True, nonnegative=True)
    Eq << sets.cup.limits.negate.apply(Cup[i:-n:n + 1](f(i)))

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.cup)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.cup)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()