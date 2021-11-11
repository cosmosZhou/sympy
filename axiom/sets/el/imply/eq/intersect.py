from util import *


@apply
def apply(given):
    A, B = given.of(Element)

    return Equal({A} & B, {A})


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << sets.el.imply.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.imply.eq.intersect.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-10-28
# updated on 2020-10-28
