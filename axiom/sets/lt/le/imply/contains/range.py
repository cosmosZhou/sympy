from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(*given):
    greater_than, _greater_than = given
    x, a = greater_than.of(Less)
    b, _x = _greater_than.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        a += 1
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
    Eq << apply(b < x, x <= a)

    #Eq << apply(x < b, a <= x)
    Eq << sets.contains.given.et.split.range.apply(Eq[-1])

    Eq << algebra.lt.given.le.apply(Eq[-1])

    Eq << algebra.ge.given.gt.apply(Eq[-2])

    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

