from util import *


@apply
def apply(*given):
    greater_than, _greater_than = given
    a, x = greater_than.of(GreaterEqual)
    b, _x = _greater_than.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x

    assert x.is_integer
    return Contains(x, Range(b, a + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    Eq << apply(x >= b, x <= a)

    #Eq << apply(b >= x, a <= x)
    Eq << sets.contains.given.et.split.range.apply(Eq[-1])

    

    Eq << algebra.lt.given.le.apply(Eq[-1])

    #Eq << Eq[-1].reversed
    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

