from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy import Symbol
from sympy.sets.contains import Contains, NotContains
from axiom.discrete import sets


# given A & B = {} => A - B = A
@plausible
def apply(given):
    assert given.is_Equality
    AB, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = AB
        AB = tmp

    assert AB.is_Intersection

    A, B = AB.args

    if A.is_FiniteSet:
        if len(A) != 1:
            swap = True
        else:
            swap = False
    else:
        swap = True
    if swap:
        A, B = B, A
        
    assert A.is_FiniteSet and len(A) == 1
    a, *_ = A.args
    
    
    return NotContains(a, B, given=given)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(integer=True)
    B = Symbol.B(dtype=dtype.integer)

    Eq << apply(Equality(a.set & B, S.EmptySet))
    
    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.contains.union)
    
    Eq << Eq[-1].intersect(a.set)
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    prove(__file__)

