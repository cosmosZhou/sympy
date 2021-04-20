from sympy import *

from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(*given):
    sufficient_A, necessary_B = given
    
    x_in_A, x_in_B = axiom.is_Sufficient(sufficient_A)
    
    _x_in_A, _x_in_B = axiom.is_Necessary(necessary_B)
    
    assert _x_in_A == x_in_A
    assert _x_in_B == x_in_B
    
    x, A = axiom.is_Contains(x_in_A)
    _x, B = axiom.is_Contains(x_in_B)
    assert x == _x
    assert not x.is_given
    assert x.is_symbol
    
    return Equal(A, B)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)
    
    Eq << apply(Sufficient(Contains(x, A), Contains(x, B)), Necessary(Contains(x, A), Contains(x, B)))
    
    Eq << Eq[0].this.apply(algebra.sufficient.to.forall, wrt=x)
    
    Eq << algebra.necessary.imply.forall.apply(Eq[1], wrt=x)
    
    Eq << sets.forall_contains.forall_contains.imply.eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    prove()

