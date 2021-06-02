from util import *


@apply
def apply(given):
    (a, x), (b, _x) = given.of(LessEqual & Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        left_open = True
        right_open = False
    else:
        left_open = False
        right_open = True

    assert x == _x

    return Contains(x, Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    Eq << apply((a <= x) & (b > x))

    Eq << Eq[1].apply(sets.contains.imply.et.split.interval)

    Eq << Eq[-1].this.find(Less).reversed
    Eq << Eq[-1].this.find(GreaterEqual).reversed


if __name__ == '__main__':
    run()