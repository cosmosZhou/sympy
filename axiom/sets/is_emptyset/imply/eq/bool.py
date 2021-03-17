from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol

from sympy.sets.contains import Contains
import axiom

from axiom import sets, algebre
from sympy import Boole
from sympy.functions.elementary.piecewise import Piecewise


# given A & B = {} => A - B = A
@apply
def apply(given, wrt=None):
    AB = axiom.is_emptyset(given)
    A, B = axiom.is_Intersection(AB)
    
    if wrt is None: 
        wrt = AB.generate_free_symbol(**AB.etype.dict)
    
    return Equality(Boole(Contains(wrt, A | B)), Boole(Contains(wrt, A)) + Boole(Contains(wrt, B)))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equality(A & B, A.etype.emptySet))
    
    Eq <<= Eq[-1].rhs.args[0].this.astype(Piecewise), Eq[-1].rhs.args[1].this.astype(Piecewise)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << sets.is_emptyset.imply.eq.piecewise.apply(Eq[0], *Eq[-1].rhs.args)
    
    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])     
    
    Eq << Eq[1].this.lhs.astype(Piecewise)

if __name__ == '__main__':
    prove(__file__)

