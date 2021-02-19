from sympy import Symbol
from sympy.sets.sets import FiniteSet
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre, sets


@apply
def apply(given):
    assert given.is_Contains
    x, domain = given.args
    assert domain == FiniteSet(0, 1)
        
    return Equality(KroneckerDelta(1, x), x)




@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    given = Contains(x, {0, 1})
    
    Eq << apply(given)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].bisect(Equality(1, x)).split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq << Eq[-2].apply(algebre.equal.unequal.imply.unequal.subs)
    
    Eq << Eq[-1].apply(algebre.condition.condition.imply.et, invert=True)
    
    Eq << Eq[-1].apply(sets.unequal.unequal.imply.notcontains, simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)


