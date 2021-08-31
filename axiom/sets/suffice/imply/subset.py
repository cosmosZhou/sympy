from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Suffice)

    x, A = x_in_A.of(Element)
    _x, B = x_in_B.of(Element)
    assert x == _x
    assert not x.is_given
    assert x.is_symbol

    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer * n)

    Eq << apply(Suffice(Element(x, A), Element(x, B)))

    Eq << Eq[0].this.apply(algebra.suffice.to.all, wrt=x)

    Eq << sets.all_el.imply.subset.apply(Eq[-1])


if __name__ == '__main__':
    run()

