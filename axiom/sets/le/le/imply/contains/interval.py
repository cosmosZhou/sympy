from util import *


@apply
def apply(*given):
    greater_than, _greater_than = given
    x, a = greater_than.of(LessEqual)
    b, _x = _greater_than.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x

    return Contains(x, Interval(b, a))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    x = Symbol.x(real=True, given=True)

#     Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, a <= x)

    Eq << sets.contains.given.et.split.interval.apply(Eq[-1])

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

