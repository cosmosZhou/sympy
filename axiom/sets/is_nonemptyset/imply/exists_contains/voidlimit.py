from sympy import *
from axiom.utility import prove, apply
from axiom import sets
# given: A != {}
# Exists[x] (x in A)


@apply
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B
    x = A.element_symbol()
    return Exists[x](Contains(x, A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    Eq << apply(Unequality(A, A.etype.emptySet))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].simplify()
    
    Eq << sets.notcontains.imply.is_emptyset.emptyset_definition.apply(Eq[-1])
    
    Eq << ~Eq[0]


if __name__ == '__main__':
    prove(__file__)

