from util import *


@apply(given=None)
def apply(given):
    x, interval = given.of(Element)
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
    from axiom import algebra, sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_interval.imply.et, simplify=False)

    Eq << Eq[-1].this.rhs.apply(sets.le.ge.imply.el.interval)


if __name__ == '__main__':
    run()

# created on 2021-03-26
