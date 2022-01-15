from util import *


@apply
def apply(ge):
    x, a = ge.of(GreaterEqual)
    assert a > 0

    return LessEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x >= a)

    Eq << algebra.ge.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * a


if __name__ == '__main__':
    run()
# created on 2019-06-02
