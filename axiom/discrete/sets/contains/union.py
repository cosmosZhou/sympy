from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from axiom.discrete.sets import subset
from sympy import Symbol
# given: A in B 
# => A | B = B
@plausible
def apply(given):
    assert given.is_Contains
    A, B = given.args
    
    return Equality(A.set | B, B, given=given)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(dtype=dtype.integer)
    contains = Contains(e, s)
    
    Eq << apply(contains)
    
    Eq << Eq[0].asSubset()
    
    Eq << subset.union.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

