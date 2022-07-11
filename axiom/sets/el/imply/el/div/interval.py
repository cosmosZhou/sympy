from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(Element)

    a, b = interval.of(Interval)

    return Element(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(real=True)
    #t = Symbol(real=True)
    d = 2
    Eq << apply(Element(x, Interval(a, b)), d)

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq << sets.el_interval.given.et.apply(Eq[1])




if __name__ == '__main__':
    run()

# created on 2018-07-08
