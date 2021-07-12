from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(GreaterEqual(x, y))
    
    Eq << ~Eq[0]
    
    #     Eq <<= Eq[1] & Eq[-1]
    
    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()