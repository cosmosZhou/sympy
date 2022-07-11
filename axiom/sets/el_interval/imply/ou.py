from util import *


@apply(simplify=False)
def apply(given, by, left_open=False):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    assert by in interval
    return Or(Element(x, Interval(a, by, left_open=interval.left_open, right_open=not left_open)), Element(x, Interval(by, b, left_open=left_open, right_open=interval.right_open)))


@prove
def prove(Eq):
    x, b = Symbol(real=True, given=True, positive=True)
    Eq << apply(Element(x, Interval(0, b)), by=b /2)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()
# created on 2020-04-12
