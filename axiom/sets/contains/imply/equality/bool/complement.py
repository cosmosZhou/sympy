from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
import axiom
from axiom import sets

@plausible
def apply(given):
    e, domain = axiom.is_Contains(given)
    _, s = axiom.is_Complement(domain)
    return Equality(bool(NotContains(e, s)), 1)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(e, S - s))
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << sets.contains.imply.notcontains.given.complement.apply(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

