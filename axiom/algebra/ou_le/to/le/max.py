from util import *


@apply(given=None)
def apply(given):
    (x, a), (S[x], b) = given.of(LessEqual | LessEqual)
    return Equivalent(given, LessEqual(x, Max(a, b)))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, a) | LessEqual(x, b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.le_max.imply.ou.le)

    Eq << Eq[-2].this.rhs.apply(algebra.le_max.given.ou.le)

    


if __name__ == '__main__':
    run()
# created on 2022-01-02
