from util import *


import axiom


@apply
def apply(*given):
    sufficient_A, sufficient_B = given
    assert sufficient_A.is_Suffice and sufficient_B.is_Suffice

    x_in_A, x_in_B = sufficient_A.of(Suffice)

    _x_in_B, _x_in_A = sufficient_B.of(Suffice)

    assert _x_in_A == x_in_A
    assert _x_in_B == x_in_B

    x, A = x_in_A.of(Contains)
    _x, B = x_in_B.of(Contains)
    assert x == _x

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(Suffice(Contains(x, A), Contains(x, B)), Suffice(Contains(x, B), Contains(x, A)))

    Eq << sets.suffice.necessary.imply.eq.apply(Eq[0], Eq[1].reversed)


if __name__ == '__main__':
    run()

