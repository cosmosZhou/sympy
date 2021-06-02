from util import *
import axiom



@apply
def apply(given, bound):
    lhs, rhs = given.of(GreaterEqual)
    
    assert bound >= rhs
    
    return GreaterEqual(lhs, bound)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(GreaterEqual(x, y), y + 1)
    
    Eq << ~Eq[0]
    
#     Eq <<= Eq[1] & Eq[-1]
    
    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

