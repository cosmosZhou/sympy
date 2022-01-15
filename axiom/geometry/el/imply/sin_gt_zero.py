from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, S.Pi, left_open=True, right_open=True)
    return Greater(sin(x), 0)


@prove(proved=False)
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi, left_open=True, right_open=True)))

    Eq << geometry.sin.to.sum.apply(sin(x))




















if __name__ == '__main__':
    run()
# created on 2020-11-19
