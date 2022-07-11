from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    assert x == _x

    return Element(x, Interval(b, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True, given=True)
    #Eq << apply(x > b, a > x)
    Eq << apply(b > x, x > a)

    Eq << sets.el_interval.given.et.apply(Eq[-1])



    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-16
