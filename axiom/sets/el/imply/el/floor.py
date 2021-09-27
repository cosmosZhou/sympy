from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    a, b = domain.of(Interval)
    assert not domain.left_open and domain.right_open
    if not b.is_integer:
        b = Ceiling(b)
    if not a.is_integer:
        a = Floor(a)
    return Element(Floor(x), Range(a, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.el.imply.el.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    Eq << Eq[-1].this.find(-~Ceiling).apply(algebra.ceiling.to.mul)

    Eq << Eq[-1].this.find(-~Floor).apply(algebra.floor.to.mul.ceiling)


if __name__ == '__main__':
    run()