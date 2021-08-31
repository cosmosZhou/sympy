from util import *


@apply
def apply(imply):
    e, AB = imply.of(Element)

    return tuple(Element(e, s) for s in AB.of(Intersection))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)


    Eq << apply(Element(x, A & B))

    Eq << sets.el.el.imply.el.intersect.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

