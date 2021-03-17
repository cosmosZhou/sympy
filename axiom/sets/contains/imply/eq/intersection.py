from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom import sets
# given: A in B 
# => A | B = B
@apply
def apply(given):
    assert given.is_Contains
    A, B = given.args
    
    return Equality(A.set & B, A.set)




@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s)
    
    Eq << apply(contains)
    
    Eq << sets.contains.imply.subset.apply(Eq[0], simplify=False)
    
    Eq << sets.subset.imply.eq.intersection.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

