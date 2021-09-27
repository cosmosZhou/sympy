from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    return GreaterEqual(Card(S), 1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    S = Symbol(etype=dtype.complex * n, given=True)
    Eq << apply(Element(x, S))

    Eq << sets.el.imply.is_nonempty.apply(Eq[0])

    Eq << sets.is_nonempty.imply.is_positive.apply(Eq[-1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()