from util import *


@apply
def apply(given, bound):
    lhs, rhs = given.of(Less)
    
    assert bound >= rhs
    
    return Less(lhs, bound)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(Less(x, y), y + 1)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[0] & Eq[-1]
    
#     Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

