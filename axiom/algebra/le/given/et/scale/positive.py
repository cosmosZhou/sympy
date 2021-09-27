from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(LessEqual)
    return lhs * scale <= rhs * scale, scale > 0


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y), z)

    Eq << algebra.is_positive.le.imply.le.div.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()