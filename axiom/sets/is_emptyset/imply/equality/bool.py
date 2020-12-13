from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol

from sympy.sets.contains import Contains
import axiom

from axiom import sets
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool


# given A & B = {} => A - B = A
@plausible
def apply(given, wrt=None):
    AB = axiom.is_emptyset(given)
    A, B = axiom.is_Intersection(AB)
    
    if wrt is None: 
        wrt = AB.generate_free_symbol(**AB.etype.dict)
    
    return Equality(bool(Contains(wrt, A | B)), bool(Contains(wrt, A)) + bool(Contains(wrt, B)))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equality(A & B, A.etype.emptySet))
    
    Eq <<= Eq[-1].rhs.args[0].this.definition, Eq[-1].rhs.args[1].this.definition
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << sets.is_emptyset.imply.equality.piecewise.apply(Eq[0], *Eq[-1].rhs.args)
    
    Eq <<= Eq[-1] & Eq[-2]     
    
    Eq << Eq[1].this.lhs.definition.reversed

if __name__ == '__main__':
    prove(__file__)

