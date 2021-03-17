from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
# given: |A| >= 1
# A != {}


@apply
def apply(given):
    assert isinstance(given, GreaterThan)
    S_abs, positive = given.args
    assert S_abs.is_Abs and positive > 1
    S = S_abs.arg

    x = S.element_symbol()
    y = S.element_symbol({x})

    return Exists[x:S, y:S](Unequality(x, y))




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(abs(S) >= 2)
    
    Eq << sets.ge.imply.exists_contains.apply(Eq[0], simplify=False)
    
    Eq << sets.exists_contains.imply.exists_contains.limits_restricted.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].apply(sets.contains.imply.eq.union)
    i = Eq[-1].variable
    
    Eq << Eq[-1].apply(algebre.eq.imply.eq.abs)
    
    Eq << sets.imply.eq.principle.addition.apply(S, i.set)
        
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1] - 1
    
    Eq << Eq[0] - 1
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq[-1].this.function.apply(sets.ge.imply.is_nonemptyset, simplify=False)
    
    i, j = Eq[1].variables
    Eq << Exists[i:S, j:S](Contains(j, Eq[-1].lhs), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << ~Eq[1]    
    
    Eq << Eq[-2].subs(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

