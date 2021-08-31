from util import *


@apply
def apply(given, left_open=True, right_open=True):
    y, x = given.of(Greater)

    return Element((x + y) / 2, Interval(x, y, right_open=right_open, left_open=left_open))


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(a > b)

    Eq << sets.lt.imply.el.interval.average.apply(Eq[0].reversed)




if __name__ == '__main__':
    run()