from util import *


@apply(given=None)
def apply(given):
    x, interval = given.of(Contains)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return Equivalent(given, And(x > a, x < b))
        else:
            return Equivalent(given, And(x > a, x <= b))
    else:
        if interval.right_open:
            return Equivalent(given, And(x >= a, x < b))
        else:
            return Equivalent(given, And(x >= a, x <= b))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(Contains(x, Interval(a, b)))

    Eq << algebra.equivalent.given.cond.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.et.split.interval, simplify=False)

    Eq << Eq[-1].this.rhs.apply(sets.le.ge.imply.contains.interval)


if __name__ == '__main__':
    run()

