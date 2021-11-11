from util import *


@apply(given=None)
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equivalent(gt, Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.gt_arg.imply.eq_ceiling)
    Eq << Eq[-1].this.lhs.apply(algebra.eq_ceiling.imply.gt_arg)


if __name__ == '__main__':
    run()
# created on 2018-10-31
# updated on 2018-10-31
