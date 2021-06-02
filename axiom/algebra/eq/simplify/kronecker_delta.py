from util import *
import axiom



@apply(given=None)
def apply(given):
    delta, one = given.of(Equal)
    if not one.is_One:
        delta, one = one, delta
    assert one.is_One

    x, y = delta.of(KroneckerDelta)

    return Equivalent(given, Equal(x, y))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))

    Eq << apply(Equal(KroneckerDelta(x, y), 1))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.lhs.astype(Piecewise)

    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)


if __name__ == '__main__':
    run()
