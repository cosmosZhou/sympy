from util import *


@apply
def apply(imply):
    e, S = imply.of(Element)
    a, b = S.of(Interval)
    assert S.right_open
    return Element(e, Interval(a, b, left_open=S.left_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True, right_open=True)))

    Eq << sets.el_interval.given.et.apply(Eq[1])

    Eq << sets.el_interval.imply.et.apply(Eq[0])
    Eq << algebra.lt.imply.le.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-28
