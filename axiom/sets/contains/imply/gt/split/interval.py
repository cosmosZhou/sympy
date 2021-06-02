from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    a, b = interval.of(Interval)

    if interval.left_open:
        return Greater(x, a)
    else:
        if interval.right_open:
            return Greater(b, x)
        else:
            ...


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << algebra.et.imply.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

