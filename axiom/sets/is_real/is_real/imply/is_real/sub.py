from util import *


@apply
def apply(a_is_real, b_is_real):
    a, aR = a_is_real.of(Element)
    b, bR = b_is_real.of(Element)
    from axiom.sets.is_real.is_real.imply.is_real import interval_is_real
    assert interval_is_real(aR)
    assert interval_is_real(bR)
    return Element(a - b, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Reals), Element(y, Reals))

    Eq << sets.el.imply.el.neg.apply(Eq[1])

    Eq << sets.is_real.is_real.imply.is_real.add.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2022-04-03
