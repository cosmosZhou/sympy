from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets


@apply(imply=True)
def apply(given):
    assert given.is_Contains
    x, domain = given.args
    assert domain == FiniteSet(0, 1)
        
    return Equality(KroneckerDelta(0, x), 1 - x)




@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    given = Contains(x, {0, 1})
    
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.astype(Piecewise)    
    
    Eq << Eq[-1].bisect(Equality(x, 0)).split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq << Eq[-2].apply(algebre.equal.unequal.imply.unequal.subs)
    
    Eq << Eq[-1].apply(algebre.condition.condition.imply.et, invert=True, reverse=True, swap=True)
    
    Eq << Eq[-1].apply(sets.unequal.unequal.imply.notcontains, simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)
