from sympy import *

from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(*given):
    sufficient_A, sufficient_B = given
    assert sufficient_A.is_Sufficient and sufficient_B.is_Sufficient
    
    x_in_A, x_in_B = axiom.is_Sufficient(sufficient_A)
    
    _x_in_B, _x_in_A = axiom.is_Sufficient(sufficient_B)
    
    assert _x_in_A == x_in_A
    assert _x_in_B == x_in_B
    
    x, A = axiom.is_Contains(x_in_A)
    _x, B = axiom.is_Contains(x_in_B)
    assert x == _x
    
    return Equality(A, B)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)
    
    Eq << apply(Sufficient(Contains(x, A), Contains(x, B)), Sufficient(Contains(x, B), Contains(x, A)))
    
    Eq << sets.sufficient.necessary.imply.equal.apply(Eq[0], Eq[1].reversed)


if __name__ == '__main__':
    prove(__file__)

