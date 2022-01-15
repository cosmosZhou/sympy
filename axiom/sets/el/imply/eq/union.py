from util import *


@apply
def apply(given, reverse=False):
    x, B = given.of(Element)
    A = x.set | B
    if reverse:
        A, B = B, A

    return Equal(x.set | B, B)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, S))

    Eq << Eq[0].apply(sets.el.imply.subset, simplify=False)

    Eq << sets.subset.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-11
