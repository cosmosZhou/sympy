from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d > 0

    e, (dom1, dom2) = given.of(Contains[Union])
    e *= d
    dom1 *= d
    dom2 *= d
    return Contains(e, dom1 | dom2)


@prove
def prove(Eq):
    from axiom import sets

    x, a, b, c, d = Symbol(real=True)
    e = Symbol(real=True, positive=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True) | Interval(c, d, right_open=True)), e)

    Eq << sets.contains.imply.ou.split.union.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(sets.contains.imply.contains.mul.interval, e)

    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.contains.mul.interval, e)

    


if __name__ == '__main__':
    run()