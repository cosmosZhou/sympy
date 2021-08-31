from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Less)

    return Element(n, Interval(-oo, b, right_open=True))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)
    Eq << apply(n < b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

from . import average
