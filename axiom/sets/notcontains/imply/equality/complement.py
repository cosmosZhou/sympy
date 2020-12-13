from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from axiom import sets

# given e not in S


# => S - {e} = S
@plausible
def apply(given):
    assert given.is_NotContains    
    e, S = given.args
    return Equality(S - {e}, S)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    e = Symbol.e(integer=True)

    Eq << apply(NotContains(e, S))
    
    Eq << sets.notcontains.imply.is_emptyset.apply(Eq[0])
    
    Eq << sets.is_emptyset.imply.equality.complement.apply(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

