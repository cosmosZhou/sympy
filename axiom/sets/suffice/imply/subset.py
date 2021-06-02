from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Suffice)

    x, A = x_in_A.of(Contains)
    _x, B = x_in_B.of(Contains)
    assert x == _x
    assert not x.is_given
    assert x.is_symbol

    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(Suffice(Contains(x, A), Contains(x, B)))

    Eq << Eq[0].this.apply(algebra.suffice.to.all, wrt=x)

    Eq << sets.all_contains.imply.subset.apply(Eq[-1])


if __name__ == '__main__':
    run()

