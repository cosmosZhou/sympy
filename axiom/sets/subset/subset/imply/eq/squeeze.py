from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    A, B = axiom.is_Subset(a_less_than_x)    
    _B, _A = axiom.is_Subset(x_less_than_b)
    assert A == _A
    assert B == _B

    return Equal(A, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.complex)
    B = Symbol.B(etype=dtype.complex)

    Eq << apply(Subset(A, B), Subset(B, A))
    
    Eq <<= Eq[0] & Eq[1]
       

    
if __name__ == '__main__':
    prove()
