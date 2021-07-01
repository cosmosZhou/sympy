from util import *


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    A, B = a_less_than_x.of(Subset)    
    _B, _A = x_less_than_b.of(Subset)
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
    run()
