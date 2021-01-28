from sympy.core.relational import Equality , StrictGreaterThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from axiom import sets, algebre
# given: |S| = 1
# Exists[x:S] ({x}) = S


@apply(imply=True)
def apply(given, var=None):
    assert given.is_Equality
    S_abs, n = given.args
    
    assert S_abs.is_Abs and n.is_extended_positive
    S = S_abs.arg
    if var is None:
        var = S.element_symbol()
    return Exists[var:S](Equality(abs(S - var.set), n - 1))




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(Equality(abs(S), n))
    
    Eq << algebre.equal.imply.greater_than.apply(Eq[0])
    
    Eq << sets.greater_than.imply.exists_contains.apply(Eq[-1], simplify=False)
    
    Eq << sets.exists_contains.imply.exists_contains.limits_restricted.apply(Eq[-1], simplify=False)
    
    i = Eq[-1].function.lhs     
    Eq << sets.imply.equal.principle.addition.apply(S, i.set)
    
    Eq << Eq[-2].apply(sets.contains.imply.equal.union)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1] - 1
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

