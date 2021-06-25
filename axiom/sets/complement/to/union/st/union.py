from util import *

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(complement, evaluate=True):
    union, C = complement.of(Complement)
    union = union.of(Union)
    return Equal(complement, Union(*(u // C for u in union), evaluate=evaluate))


@prove
def prove(Eq):
    from axiom import sets
    B = Symbol.B(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    Eq << apply((A | B) // C, evaluate=False)

    A = Symbol.A(A // C)
    B = Symbol.B(B // C)

    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition

    Eq << sets.eq.eq.imply.eq.union.apply(Eq.A_definition, Eq.B_definition)

    Eq << Eq[0].this.rhs.subs(Eq.A_definition.reversed, Eq.B_definition.reversed)

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

