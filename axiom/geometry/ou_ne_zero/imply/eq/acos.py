from util import *


@apply
def apply(ou, reverse=False):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    y = abs(y)
    lhs, rhs = acos(x / r), Piecewise((asin(y / r), x >= 0), (S.Pi - asin(y / r), True))
    if reverse:
        lhs, rhs = rhs, lhs
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Eq[-1].this.lhs.apply(geometry.acos.to.add.asin)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=x >= 0)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq.x_is_nonnegative, Eq.x_is_negative = Eq[-2].this.find(acos).apply(geometry.acos.to.piece.asin), Eq[-1].this.find(acos).apply(geometry.acos.to.piece.asin)

    Eq.sqrt_is_positive = algebra.ou_ne_zero.imply.sqrt_gt_zero.apply(Eq[0])

    Eq << algebra.cond.imply.infer.et.apply(Eq.sqrt_is_positive, cond=Eq.x_is_nonnegative.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.ge.imply.ge.div)

    Eq <<= Eq.x_is_nonnegative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.bool, index=1)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(algebra.add.to.mul.together)

    Eq << algebra.cond.imply.infer.et.apply(Eq.sqrt_is_positive, cond=Eq.x_is_negative.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.lt.imply.lt.div)

    Eq <<= Eq.x_is_negative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.bool, index=1, invert=True)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(algebra.add.to.mul.together)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2020-12-03
# updated on 2020-12-03
