from util import *


@apply
def apply(gt_a, gt_b):
    x, a = gt_a.of(Greater)
    S[x], b = gt_b.of(Greater)
    return x > Max(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x > y, x > b)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True, reverse=True)

    


if __name__ == '__main__':
    run()
# created on 2019-03-09
# updated on 2022-01-03