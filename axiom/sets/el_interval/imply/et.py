from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
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

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(a, b)))



    Eq << sets.el_interval.imply.le.apply(Eq[0])

    Eq << sets.el_interval.imply.ge.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-04-05
