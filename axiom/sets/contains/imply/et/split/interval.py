from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return x > a, x < b
        else:
            return x > a, x <= b
    else:
        if interval.right_open:
            return x >= a, x < b
        else:
            return x >= a, x <= b


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b)))

    

    Eq << sets.contains.imply.le.split.interval.apply(Eq[0])

    Eq << sets.contains.imply.ge.split.interval.apply(Eq[0])


if __name__ == '__main__':
    run()

