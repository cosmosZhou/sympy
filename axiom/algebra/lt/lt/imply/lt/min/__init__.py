from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True, reverse=True)

    
    


if __name__ == '__main__':
    run()

from . import both
# created on 2019-05-12
# updated on 2022-01-03