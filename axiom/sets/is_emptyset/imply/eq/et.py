from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
# given: A | B = {}
# A = {} and B = {}


@apply
def apply(given):
    assert given.is_Equal
    AB, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = AB
        AB = tmp
        assert emptyset.is_EmptySet

    assert AB.is_Union
    A, B = AB.args
    emptySet = A.etype.emptySet
    return And(Equal(A, emptySet), Equal(B, emptySet))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq.ou = ~Eq[-1]

    Eq.A_nonempty = Eq.ou.args[0].copy(plausible=True)
    
    Eq.B_nonempty = Eq.ou.args[1].copy(plausible=True)    

    Eq.A_positive = Eq.A_nonempty.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.B_positive = Eq.B_nonempty.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.AB_union_empty = Eq[0].apply(algebra.eq.imply.eq.abs)
    
    Eq << sets.eq.imply.eq.complement.apply(Eq[0], A)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq.A_positive.subs(Eq[-1].reversed)

    Eq << sets.eq.imply.eq.complement.apply(Eq[0], B)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq.B_positive.subs(Eq[-1].reversed)

    Eq << ~Eq.A_nonempty
    
    Eq << ~Eq.B_nonempty

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove()

