from util import *


@apply
def apply(given, factor):
    lhs, rhs = given.of(Greater)

    assert factor > 0

    return Greater(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True, given=True)
    k = Symbol(real=True, given=True, positive=True)

    Eq << apply(Greater(x, y), k)

    Eq << Greater(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.gt_zero.imply.gt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-07-23
# updated on 2019-07-23
