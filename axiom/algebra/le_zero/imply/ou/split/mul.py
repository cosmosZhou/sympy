from util import *


@apply
def apply(given):
    x, y = given.of(Mul <= 0)
    return Or(And(x >= 0, y <= 0), And(x <= 0, y >= 0))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True, given=True)

    Eq << apply(x * y <= 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(algebra.ou.imply.ou.invert, pivot=1)

    Eq << Eq[-1].this.args[1].apply(algebra.ou.imply.ou.invert, pivot=1)

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[1].apply(algebra.et.imply.ou)

    Eq << Eq[-1].this.args[-1].apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].apply(algebra.lt_zero.lt_zero.imply.gt_zero)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-05-30
