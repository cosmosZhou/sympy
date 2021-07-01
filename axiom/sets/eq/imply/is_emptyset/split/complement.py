from util import *


@apply
def apply(given):
    (A, B), _A = given.of(Equal[Complement])
    assert _A == A

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equal(A // B, A))

    Eq << Eq[0].apply(sets.eq.imply.eq.intersection, B).reversed


if __name__ == '__main__':
    run()

