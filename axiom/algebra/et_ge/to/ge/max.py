from util import *


@apply(given=None)
def apply(et):
    ge_a, ge_b = et.of(And)
    x, a = ge_a.of(GreaterEqual)
    S[x], b = ge_b.of(GreaterEqual)
    return Equivalent(et, x >= Max(a, b), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(And(x >= y, x >= b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge.ge.imply.ge.max.rhs)

    Eq << Eq[-1].this.lhs.apply(algebra.ge.ge.given.ge.max)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
