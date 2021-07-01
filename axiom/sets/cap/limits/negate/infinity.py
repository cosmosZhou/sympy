from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cap)
    return Equal(self, Cap[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, calculus

    i = Symbol.i(integer=True)
    f = Function.f(etype=dtype.real)
    Eq << apply(Cap[i](f(i)))

    n = Symbol.n(integer=True, nonnegative=True)
    Eq << sets.cap.limits.negate.apply(Cap[i:-n:n + 1](f(i)))

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.cap)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.cap)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()