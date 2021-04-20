from sympy.core.relational import Equal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.sets.contains import NotContains
from axiom import sets


# given A & B = {} => A - B = A
@apply
def apply(given):
    assert given.is_Equal
    AB, emptyset = given.args
    if emptyset:
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
    
    
    return NotContains(a, B)




@prove
def prove(Eq):
    a = Symbol.a(integer=True, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equal(a.set & B, a.emptySet))
    
    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.contains.imply.eq.union)
    
    Eq << Eq[-1].apply(sets.eq.imply.eq.intersect, a.set)
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    prove()

