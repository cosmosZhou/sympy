from util import *


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    assert x == _x
    assert x.is_integer
    return Element(x, Range(b + 1, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(integer=True, given=True)
    #Eq << apply(x > b, a > x)
    Eq << apply(b > x, x > a)

    Eq << sets.el.given.et.split.range.apply(Eq[-1])

    Eq << algebra.ge.given.gt.apply(Eq[-2])

    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

