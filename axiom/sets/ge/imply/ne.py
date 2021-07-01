from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(given):
    assert isinstance(given, GreaterEqual)
    A_abs, positive = given.args
    assert A_abs.is_Abs and positive.is_positive
    A = A_abs.arg

    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import algebra
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(abs(A) >= 1)

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

