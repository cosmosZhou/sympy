from axiom.utility import prove, apply
from sympy import *

from axiom import sets
import axiom


@apply
def apply(given):
    assert given.is_Subset
    B, A = given.args
    e = axiom.is_FiniteSet(B)
   
    return Contains(e, A)


@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    e = Symbol.e(complex=True, shape=(n,))
    B = {e}
    
    Eq << apply(Subset(B, A))
    
    Eq << sets.subset.imply.forall_contains.apply(Eq[0])


if __name__ == '__main__':
    prove(__file__)

