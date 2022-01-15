from util import *


@apply(given=None)
def apply(et):
    gt_a, gt_b = et.of(And)
    x, a = gt_a.of(Greater)
    S[x], b = gt_b.of(Greater)
    return Equivalent(et, x > Max(a, b), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(And(x > y, x > b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.gt.gt.imply.gt.max.rhs)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.gt.given.gt.max)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
