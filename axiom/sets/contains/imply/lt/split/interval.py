from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    a, b = interval.of(Interval)

    if interval.right_open:
        return Less(x, b)
    else:
        if interval.left_open:
            return Less(a, x)

@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    


if __name__ == '__main__':
    run()

