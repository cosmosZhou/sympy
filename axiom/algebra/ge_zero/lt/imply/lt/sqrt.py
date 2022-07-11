from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    _x, M = lt.of(Less)
    assert x == _x

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x < M)

    Eq << algebra.ge.lt.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])

    Eq << algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[0])

    Eq << algebra.gt.ge.imply.gt.add.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.imply.lt_zero.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul.st.square_difference)

    Eq << algebra.gt_zero.lt.imply.lt.div.apply(Eq[-3], Eq[-1])

    Eq << algebra.lt_zero.imply.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-28
