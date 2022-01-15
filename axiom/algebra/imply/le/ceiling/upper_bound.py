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

    Eq << algebra.lt.imply.le.floor.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-10-02
