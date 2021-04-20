from axiom.utility import prove, apply
from sympy import *
from axiom import sets


# given: A ∈ B 
# => A ∪ B = B
@apply
def apply(given):
    assert given.is_Contains
    A, B = given.args
    
    return Equal(A.set | B, B)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s)
    
    Eq << apply(contains)
    
    Eq << Eq[0].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << sets.subset.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    prove()

