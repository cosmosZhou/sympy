
from axiom.utility import prove, apply

from sympy import *


@apply(imply=True)
def apply(*given):
    contains1, contains2 = given
    assert contains1.is_Contains    
    assert contains2.is_Contains
    
    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A
    
    return Subset({x, y}, A)




@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S), Contains(y, S))
    
    Eq << Eq[-1].definition
    
    Eq << Eq[-1].split()
    
if __name__ == '__main__':
    prove(__file__)

