from util import *


@apply
def apply(given):
    x = given.of(Unequal[Abs, 0])
    return Unequal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(abs(x), 0))

    Eq << ~Eq[1]



    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-08-01
