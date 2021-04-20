from sympy import *

from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(eq, wrt=None):
    A, B = axiom.is_Equal(eq)
    if wrt is None:
        wrt = eq.generate_free_symbol(**A.etype.dict)
        
    return Sufficient(Contains(wrt, A), Contains(wrt, B)), Sufficient(Contains(wrt, B), Contains(wrt, A))

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)
    
    Eq << apply(Equal(A, B), wrt=x)
    
    Eq << sets.sufficient.sufficient.imply.eq.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    prove()

