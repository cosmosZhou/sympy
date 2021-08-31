from util import *



@apply
def apply(given, t):
    assert given.is_Element

    e, interval = given.args

    return Element(e + t, interval + t)


@prove
def prove(Eq):
    from axiom import sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << sets.el.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-1] + t, Eq[-2] + t

    Eq << sets.le.ge.imply.el.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

