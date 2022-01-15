from util import *


@apply
def apply(given, t):
    x = given.of(Expr > 0)
    assert t > 1
    return Greater(t * x, x)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(real=True, given=True)
    t = Symbol(integer=True, positive=True, even=True)
    Eq << apply(a > 0, t)

    Eq << Greater(t - 1, 0, plausible=True)

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)
    Eq << algebra.gt_zero.imply.gt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-14
