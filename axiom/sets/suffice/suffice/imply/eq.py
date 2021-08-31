from util import *




@apply
def apply(sufficient_A, sufficient_B):
    assert sufficient_A.is_Suffice and sufficient_B.is_Suffice

    x_in_A, x_in_B = sufficient_A.of(Suffice)

    _x_in_B, _x_in_A = sufficient_B.of(Suffice)

    assert _x_in_A == x_in_A
    assert _x_in_B == x_in_B

    x, A = x_in_A.of(Element)
    _x, B = x_in_B.of(Element)
    assert x == _x

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer * n)

    Eq << apply(Suffice(Element(x, A), Element(x, B)), Suffice(Element(x, B), Element(x, A)))

    Eq << sets.suffice.necessary.imply.eq.apply(Eq[0], Eq[1].reversed)


if __name__ == '__main__':
    run()

