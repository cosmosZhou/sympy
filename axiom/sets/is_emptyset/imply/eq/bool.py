from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebra


# given A & B = {} => A - B = A
@apply
def apply(given, wrt=None):
    AB = axiom.is_emptyset(given)
    A, B = axiom.is_Intersection(AB)
    
    if wrt is None: 
        wrt = AB.generate_free_symbol(**AB.etype.dict)
    
    return Equal(Bool(Contains(wrt, A | B)), Bool(Contains(wrt, A)) + Bool(Contains(wrt, B)))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equal(A & B, A.etype.emptySet))
    
    Eq <<= Eq[-1].rhs.args[0].this.definition, Eq[-1].rhs.args[1].this.definition
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << sets.is_emptyset.imply.eq.piecewise.apply(Eq[0], *Eq[-1].rhs.args)
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])     
    
    Eq << Eq[1].this.lhs.definition


if __name__ == '__main__':
    prove()

