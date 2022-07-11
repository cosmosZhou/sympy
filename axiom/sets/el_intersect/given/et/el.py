from util import *


@apply
def apply(imply, index=-1):
    e, args = imply.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])

    return Element(e, first), Element(e, second)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, A & B))

    Eq << sets.el.el.imply.el.intersect.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2018-09-23
