from util import *


@apply
def apply(given):
    x, y = given.of(Equal)

    return Equal(floor(x), floor(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Equal(x, y))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
