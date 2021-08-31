from util import *


@apply
def apply(x):
    return LessEqual(Ceiling(x), floor(x) + 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, given=True)

    Eq << apply(x)

    Eq << algebra.imply.lt.ceiling.apply(x)

    Eq << ~Eq[0]

    Eq << algebra.lt.gt.imply.lt.transit.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

