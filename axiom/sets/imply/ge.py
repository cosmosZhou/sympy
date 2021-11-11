from util import *


@apply
def apply(A, B):
    return GreaterEqual(Card(Union(A, B)), Card(A))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << Eq[-1].lhs.arg.this.apply(sets.union.rewrite.complement, index=0)

    Eq << sets.eq.imply.eq.card.apply(Eq[-1])

    Eq << Eq[-1] + GreaterEqual(Eq[-1].rhs.args[1], 0, plausible=True)

    Eq << Eq[-1].this.apply(algebra.ge.simplify.common_terms)


if __name__ == '__main__':
    run()

# created on 2020-08-09
# updated on 2020-08-09
