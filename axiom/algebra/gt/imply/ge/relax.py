from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    
    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(x > y)    

    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]    


if __name__ == '__main__':
    run()