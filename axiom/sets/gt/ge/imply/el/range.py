from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    _x, b = _greater_than.of(GreaterEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        a += 1
        b += 1

    assert x == _x
    assert x.is_integer
    return Element(x, Range(b, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(integer=True, given=True)
    Eq << apply(x > b, a >= x)

    #Eq << apply(b > x, x >= a)
    Eq << sets.el_range.given.et.apply(Eq[-1])

    Eq <<= algebra.lt.given.le.apply(Eq[-1]), algebra.ge.given.gt.apply(Eq[-2])

    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-13
