from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom import sets
# given: A ∈ B 
# => A ∪ B = B
@apply(imply=True)
def apply(given):
    assert given.is_Contains
    A, B = given.args
    
    return Equality(A.set | B, B)




@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s)
    
    Eq << apply(contains)
    
    Eq << Eq[0].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << sets.subset.imply.equal.union.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

