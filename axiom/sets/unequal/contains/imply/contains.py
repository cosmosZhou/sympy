from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets
# given: x != y
# x not in {y}


@apply
def apply(*given):
    inequality, contains = given
    _x, y = axiom.is_Unequal(inequality)
    x, s = axiom.is_Contains(contains)
    
    if x != _x:
        _x, y = y, _x
    assert x == _x
    
    return Contains(x, s - y.set)




@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    s = Symbol.s(etype=dtype.integer, given=True)
    Eq << apply(Unequality(x, y), Contains(x, s))
    
    Eq << sets.unequal.imply.notcontains.apply(Eq[0], simplify=False)
    
    Eq <<= Eq[-1] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

