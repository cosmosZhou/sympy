from util import *


@apply
def apply(given):
    (x, a), (b, _x) = given.of(LessEqual & LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x

    assert x == _x

    return Contains(x, Interval(b, a, left_open=False, right_open=False))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    Eq << apply((a <= x) & (x <= b))

    Eq << Eq[1].apply(sets.contains.imply.et.split.interval)

    Eq << Eq[-1].this.find(GreaterEqual).reversed


if __name__ == '__main__':
    run()