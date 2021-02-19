from sympy import *
from axiom.utility import prove, apply


@apply
def apply(*given):
    contains1, contains2 = given
    assert contains1.is_Contains    
    assert contains2.is_Contains
    
    e, A = contains1.args
    _e, B = contains2.args
    assert e == _e
    
    return Contains(e, A & B)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)    

    Eq << apply(Contains(e, A), Contains(e, B))
        
    Eq <<= Eq[0] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

