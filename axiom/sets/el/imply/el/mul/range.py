from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])

    e *= d

    return Element(e, Range(a * d, (b - 1) * d + 1))


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b)), d)

    Eq << sets.el_range.imply.et.apply(Eq[0], right_open=False)

    Eq <<= Eq[-1] * d, Eq[-2] * d

    Eq << sets.ge.le.imply.el.range.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2018-05-26
