from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(GreaterEqual)
    return lhs * scale <= rhs * scale, scale < 0


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, y), z)
    Eq << algebra.lt_zero.le.imply.ge.div.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-05-22
# updated on 2019-05-22
