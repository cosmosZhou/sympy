from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)

    return Contains(n, Interval(b, oo, left_open=True))


@prove
def prove(Eq):
    n = Symbol.n(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(n > b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

