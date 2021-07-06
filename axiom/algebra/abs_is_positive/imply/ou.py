from util import *


@apply(simplify=None)
def apply(given):
    x = given.of(Abs > 0)
    return Or(x < 0, x > 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(abs(x) > 0)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(algebra.le.ge.imply.eq)

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()