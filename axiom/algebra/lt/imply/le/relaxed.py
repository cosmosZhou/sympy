from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(given):
    assert given.is_Less
    lhs, rhs = given.args
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(x < y)   
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove()
