from util import *


@apply(given=None)
def apply(given):
    (x, a), (S[x], b) = given.of(GreaterEqual | GreaterEqual)
    return Equivalent(given, GreaterEqual(x, Min(a, b)))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, a) | GreaterEqual(x, b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.ge_min.imply.ou.ge)

    Eq << Eq[-2].this.rhs.apply(algebra.ge_min.given.ou.ge)


if __name__ == '__main__':
    run()
# created on 2022-01-02
