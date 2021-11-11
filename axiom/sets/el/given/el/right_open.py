from util import *


@apply
def apply(imply):
    e, S = imply.of(Element)
    a, b = S.of(Interval)
    assert not S.right_open
    return Element(e, Interval(a, b, left_open=S.left_open, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))
    Eq << sets.el.imply.el.right_close.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-03-01
# updated on 2021-03-01
