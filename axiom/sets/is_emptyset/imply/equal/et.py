from sympy.core.relational import Equality
from sympy import Symbol
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from axiom import sets, algebre
from sympy.logic.boolalg import And

# given: A | B = {}
# A = {} and B = {}


@apply(imply=True)
def apply(given):
    assert given.is_Equality
    AB, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = AB
        AB = tmp
        assert emptyset.is_EmptySet

    assert AB.is_Union
    A, B = AB.args
    emptySet = A.etype.emptySet
    return And(Equality(A, emptySet), Equality(B, emptySet))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equality(A | B, A.etype.emptySet))

    Eq << ~Eq[-1]

    Eq.A_nonempty, Eq.B_nonempty = Eq[-1].split()

    Eq.A_positive = Eq.A_nonempty.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.B_positive = Eq.B_nonempty.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.AB_union_empty = Eq[0].apply(algebre.equal.imply.equal.abs)

    Eq << Eq[0] - A

    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)

    Eq << sets.imply.equal.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq[-1].subs(Eq.A_positive)

    Eq << Eq[0] - B

    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)

    Eq << sets.imply.equal.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq[-1].subs(Eq.B_positive)

    Eq << ~Eq.A_nonempty
    Eq << ~Eq.B_nonempty

    Eq << (Eq[-1] & Eq[-2])


if __name__ == '__main__':
    prove(__file__)

