from util import *



@apply(given=None)
def apply(given):
    x, y = given.of(Equal[KroneckerDelta, 1])
    return Equivalent(given, Equal(x, y))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n,))

    Eq << apply(Equal(KroneckerDelta(x, y), 1))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.lhs.apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.kroneckerDelta.to.piece)


if __name__ == '__main__':
    run()
# created on 2019-04-20
# updated on 2019-04-20
