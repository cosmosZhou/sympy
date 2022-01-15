from util import *


@apply(simplify=None)
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(1 / x, 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0))

    Eq << ~Eq[-1]

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-02-15
