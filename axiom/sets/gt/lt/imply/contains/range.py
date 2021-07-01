from util import *


@apply
def apply(*given):
    greater_than, _greater_than = given
    a, x = greater_than.of(Greater)
    b, _x = _greater_than.of(Less)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    b += 1

    assert x == _x
    assert x.is_integer
    return Contains(x, Range(b, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    Eq << apply(x > b, x < a)

    #Eq << apply(b > x, a < x)
    Eq << sets.contains.given.et.split.range.apply(Eq[-1])

    

    Eq << algebra.ge.given.gt.apply(Eq[-1])

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

