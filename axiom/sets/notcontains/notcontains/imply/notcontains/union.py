from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(*given):
    notcontains1, notcontains2 = given
    assert notcontains1.is_NotContains    
    assert notcontains2.is_NotContains
    
    e, A = notcontains1.args
    _e, B = notcontains2.args
    assert e == _e
    
    return NotContains(e, (A | B).simplify())


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)    

    Eq << apply(NotContains(e, A), NotContains(e, B))
    
    Eq <<= Eq[0] & Eq[1]

    
if __name__ == '__main__':
    prove()

