from util import *



@apply(given=None)
def apply(given):
    x, y = given.of(Equal[KroneckerDelta, 1])
    return Equivalent(given, Equal(x, y))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))

    Eq << apply(Equal(KroneckerDelta(x, y), 1))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.lhs.apply(algebra.kroneckerDelta.to.piecewise)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.kroneckerDelta.to.piecewise)


if __name__ == '__main__':
    run()
