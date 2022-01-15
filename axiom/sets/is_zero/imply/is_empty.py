from util import *


@apply
def apply(given):
    A = given.of(Equal[0])
    A = A.of(Card)

    return Equal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(A), 0))

    Eq << ~Eq[-1]

    Eq << sets.ne_empty.imply.ne_zero.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()

# created on 2020-07-20
