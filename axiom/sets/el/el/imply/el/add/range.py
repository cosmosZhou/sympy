from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    assert S0.is_Range and S1.is_Range

    return Element(x0 + x1, S0 + S1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, d, x0, x1 = Symbol(integer=True)
    Eq << apply(Element(x0, Range(a, b)), Element(x1, Range(c, d)))

    Eq << sets.el.imply.et.split.range.apply(Eq[0])

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << sets.el.imply.et.split.range.apply(Eq[1])

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq <<= Eq[-1] + Eq[-4], Eq[-3] + Eq[3]


    Eq << sets.le.ge.imply.el.range.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
