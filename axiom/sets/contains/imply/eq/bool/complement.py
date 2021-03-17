from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy.core.relational import Equality
from sympy import Symbol, Boole
import axiom
from axiom import sets
from sympy.functions.elementary.piecewise import Piecewise

@apply
def apply(given):
    e, domain = axiom.is_Contains(given)
    _, s = axiom.is_Complement(domain)
    return Equality(Boole(NotContains(e, s)), 1)




@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(e, S - s))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << sets.contains.imply.notcontains.having.complement.apply(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

