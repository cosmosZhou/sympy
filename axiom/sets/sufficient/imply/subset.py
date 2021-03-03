from sympy import *

from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(given):
    x_in_A, x_in_B = axiom.is_Sufficient(given)
    
    x, A = axiom.is_Contains(x_in_A)
    _x, B = axiom.is_Contains(x_in_B)
    assert x == _x
    assert not x.is_given
    assert x.is_symbol
    
    return Subset(A, B)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)
    
    Eq << apply(Sufficient(Contains(x, A), Contains(x, B)))
    
    Eq << algebre.sufficient.imply.forall.rewrite.apply(Eq[0], wrt=x)
    
    Eq << sets.forall_contains.imply.subset.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

