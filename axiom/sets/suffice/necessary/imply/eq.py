from util import *




@apply
def apply(*given):
    sufficient_A, necessary_B = given

    x_in_A, x_in_B = sufficient_A.of(Suffice)

    _x_in_A, _x_in_B = necessary_B.of(Necessary)

    assert _x_in_A == x_in_A
    assert _x_in_B == x_in_B

    x, A = x_in_A.of(Contains)
    _x, B = x_in_B.of(Contains)
    assert x == _x
    assert not x.is_given
    assert x.is_symbol

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(Suffice(Contains(x, A), Contains(x, B)), Necessary(Contains(x, A), Contains(x, B)))

    Eq << Eq[0].this.apply(algebra.suffice.to.all, wrt=x)

    Eq << algebra.necessary.imply.all.apply(Eq[1], wrt=x)

    Eq << sets.all_contains.all_contains.imply.eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

