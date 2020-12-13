from sympy import Symbol
from sympy.sets.sets import FiniteSet
from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre, sets


@plausible
def apply(given):
    assert given.is_Contains
    x, domain = given.args
    assert domain == FiniteSet(0, 1)
        
    return Equality(KroneckerDelta(0, x), 1 - x)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    given = Contains(x, {0, 1})
    
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.astype(Piecewise)    
    
    Eq << Eq[-1].bisect(Equality(x, 0)).split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq << Eq[-2].apply(algebre.equality.inequality.imply.inequality)
    
    Eq << Eq[-1].apply(algebre.inequality.inequality.imply.et, bool=True, invert=True, reverse=True, swap=True)
    
    Eq << Eq[-1].apply(sets.inequality.inequality.imply.notcontains, simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)
