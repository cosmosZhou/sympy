from util import *


@apply(given=None)
def apply(given):
    x, interval = given.of(Element)
    return Equivalent(given, Element(-x, -interval))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq <<= Eq[-2].apply(algebra.infer.given.ou), Eq[-1].apply(algebra.assuming.given.ou)

    Eq << Eq[-2].this.args[0].apply(sets.el.given.el.neg)

    Eq << Eq[-1].this.args[1].apply(sets.el.given.el.neg)


if __name__ == '__main__':
    run()

# created on 2018-10-06
