from util import *


@apply
def apply(given, scale, div=False):
    lhs, rhs = given.of(LessEqual)
    if div:
        le = lhs / scale <= rhs / scale
    else:
        le = lhs * scale <= rhs * scale
    return le, scale > 0


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y), z, div=True)

    Eq << algebra.gt_zero.le.imply.le.mul.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-19
# updated on 2019-08-19
