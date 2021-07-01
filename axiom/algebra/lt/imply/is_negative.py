from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Less(x - y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0] - y


if __name__ == '__main__':
    run()
