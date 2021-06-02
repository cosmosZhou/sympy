from util import *
import axiom



@apply
def apply(given, factor):
    lhs, rhs = given.of(Less)

    assert factor > 0

    return Less(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    k = Symbol.k(real=True, given=True, positive=True)

    Eq << apply(Less(x, y), k)

    Eq << Greater(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << algebra.is_positive.is_negative.imply.is_negative.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.is_negative.imply.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()

