from util import *


@apply
def apply(imply, c):
    e, interval = imply.of(Element)
    assert c.is_finite

    return Element(e + c, interval + c)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True)
    a, b, c = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), c=c)

    Eq << sets.el.imply.le.split.interval.apply(Eq[1])

    Eq << sets.el.imply.ge.split.interval.apply(Eq[1])

    Eq << sets.el.given.et.split.interval.apply(Eq[0])


if __name__ == '__main__':
    run()

