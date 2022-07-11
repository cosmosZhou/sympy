from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d > 0

    e, (dom1, dom2) = given.of(Element[Union])
    e /= d
    dom1 /= d
    dom2 /= d
    return Element(e, dom1 | dom2)


@prove
def prove(Eq):
    from axiom import sets

    x, a, b, c, d = Symbol(real=True)
    e = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True) | Interval(c, d, right_open=True)), e)

    Eq << sets.el_union.imply.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(sets.el.imply.el.div.interval, e)

    Eq << Eq[-1].this.args[0].apply(sets.el.imply.el.div.interval, e)


if __name__ == '__main__':
    run()
# created on 2021-03-04
