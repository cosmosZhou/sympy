from util import *


@apply(given=None)
def apply(et):
    lt_a, lt_b = et.of(And)
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return Equivalent(et, x < Min(a, b), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(And(x < y, x < b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.lt.lt.imply.lt.min)

    Eq << Eq[-1].this.lhs.apply(algebra.lt.lt.given.lt.min)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
