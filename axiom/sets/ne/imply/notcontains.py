from sympy import *
from axiom.utility import prove, apply
# given: x != y
# x not in {y}


@apply(simplify=None)
def apply(given):
    assert given.is_Unequality
    x, y = given.args
    return NotContains(x, y.set)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequality(x, y))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].simplify()
    
    Eq <<= Eq[-1] & Eq[0]    
    

if __name__ == '__main__':
    prove(__file__)

