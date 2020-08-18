from sympy.core.relational import Equality 
from sympy.utility import plausible
from sympy.core.symbol import dtype, Symbol

from sympy.concrete.expr_with_limits import Exists, ForAll
from axiom.discrete import sets
# given: |S| = 1
# Exists[x:S] ({x}) = S


@plausible
def apply(given):
    assert given.is_Equality
    S_abs, one = given.args
    
    assert S_abs.is_Abs and one == 1
    S = S_abs.arg
    x = S.element_symbol()
    return Exists(Equality(x.set, S), (x,), given=given)


from sympy.utility import check


@check
def prove(Eq):
    S = Symbol('S', dtype=dtype.integer)

    Eq << apply(Equality(abs(S), 1))
    
    Eq << Eq[0].subs(1, 0)
    
    Eq << sets.positive.inequality.apply(Eq[-1])
    
    Eq << sets.inequality.contains.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.asSubset()
    
    Eq << Eq[-1].apply(sets.subset.equality.equality, Eq[0])


if __name__ == '__main__':
    prove(__file__)

