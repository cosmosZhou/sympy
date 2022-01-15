from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    S[x], b = ge_b.of(GreaterEqual)
    return x >= Max(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= y, x >= b)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True, reverse=True)

    


if __name__ == '__main__':
    run()
# created on 2019-05-16
# updated on 2022-01-03