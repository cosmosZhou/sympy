from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(given):
    assert given.is_Less
    lhs, rhs = given.args
    assert lhs.is_integer and rhs.is_integer
    return LessEqual(lhs, rhs - 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    Eq << apply(x < y)   
    
    Eq << Contains(x, Interval(-oo, y, right_open=True, integer=True), plausible=True) 
    
    Eq << Eq[-1].simplify()
    
    Eq << sets.contains.imply.contains.interval.add.apply(Eq[-1], 1, simplify=False)
    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])
    
    Eq << Eq[-1] - 1
    

if __name__ == '__main__':
    prove()
