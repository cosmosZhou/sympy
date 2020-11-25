from sympy.core.relational import Equality , StrictGreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.concrete.expr_with_limits import Exists
from axiom import sets
# given: |S| = 1
# Exists[x:S] ({x}) = S


@plausible
def apply(given):
    assert given.is_Equality
    S_abs, n = given.args
    
    assert S_abs.is_Abs and n.is_extended_positive
    S = S_abs.arg
    x = S.element_symbol()
    return Exists[x](Equality(x.set, S), given=given)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Equality(abs(S), 1))
    
    Eq << StrictGreaterThan(abs(S), 0, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[-1])
    
    Eq << sets.is_nonemptyset.imply.exists_contains.emptyset.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << Eq[-1].apply(sets.subset.equality.imply.equality, Eq[0])


if __name__ == '__main__':
    prove(__file__)


