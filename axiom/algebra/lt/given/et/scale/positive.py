from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(Less)
    return lhs * scale < rhs * scale, scale > 0


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Less(x, y), z)
    
    Eq << algebra.is_positive.lt.imply.lt.div.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()