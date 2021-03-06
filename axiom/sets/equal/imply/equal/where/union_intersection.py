from axiom.utility import prove, apply

from sympy import *
# given : A & B = A | B => A = B


@apply(imply=True)
def apply(given):
    assert given.is_Equality
    assert given.lhs.is_Intersection and given.rhs.is_Union or given.lhs.is_Union and given.rhs.is_Intersection
    A, B = given.lhs.args
    _A, _B = given.rhs.args
    assert A == _A and B == _B
    return Equality(A, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equality(A & B, A | B))
    
    Eq << Subset(A, A | B, plausible=True).subs(Eq[0].reversed)    
    Eq << Subset(A & B, B, plausible=True)
    
    Eq.subset = Eq[-2].subs(Eq[-1])

    Eq << Subset(B, A | B, plausible=True).subs(Eq[0].reversed)    
    Eq << Subset(A & B, A, plausible=True)
    
    Eq << Eq[-2].subs(Eq[-1]).subs(Eq.subset).reversed


if __name__ == '__main__':
    prove(__file__)

