from util import *


@apply(given=None)
def apply(gt):
    x, a = gt.of(Abs > Expr)
    return Equivalent(gt, Or(x < -a, x > a), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) > a)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.abs_gt.imply.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.abs_gt.given.ou)


if __name__ == '__main__':
    run()
# created on 2022-01-07
