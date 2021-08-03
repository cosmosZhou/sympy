from util import *


@apply
def apply(eq):
    ((A, B), pi2), half = eq.of(Equal[Ceiling[(Arg + Arg) * Expr - Expr], 1])
    assert half * 2 == 1
    assert 1 / pi2 == S.Pi * 2
    return Arg(A) + Arg(B) > S.Pi


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1))

    Eq << algebra.eq.imply.is_positive.apply(Eq[0])

    Eq << algebra.ceiling_is_positive.imply.is_positive.apply(Eq[-1])

    Eq << algebra.is_positive.imply.gt.apply(Eq[-1])
    Eq << Eq[-1] * S.Pi * 2


if __name__ == '__main__':
    run()