from util import *

# A \ (B \ C) = (A \ B) | (A & B & C)


@apply
def apply(complement, evaluate=False):
    A, BC = complement.of(Complement)
    B, C = BC.of(Complement)
    return Equal(complement, Union(A - B, A & B & C, evaluate=evaluate))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(A - (B - C))

    D = Symbol(A - B)
    I = Symbol(A & B)
    Eq << Equal(A, D | I, plausible=True)

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.find(Complement, Complement).args[1].definition

    Eq << Eq[0].lhs.this.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(sets.complement.to.union.st.union)

    Eq << Eq[-1].this.rhs.subs(D.this.definition)

    Eq << (C & I).this.args[1].definition

    Eq << Eq[0].rhs.this.subs(Eq[-1].reversed)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-09
# updated on 2018-01-09
