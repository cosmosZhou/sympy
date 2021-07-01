from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(*given):
    greater_than, _greater_than = given
    a, x = greater_than.of(Greater)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    assert x == _x

    return Contains(x, Interval(b, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    #Eq << apply(x > b, a > x)
    Eq << apply(b > x, x > a)

    Eq << sets.contains.given.et.split.interval.apply(Eq[-1])

    

    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

