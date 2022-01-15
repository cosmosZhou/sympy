from util import *


@apply(given=None)
def apply(et):
    le_a, le_b = et.of(And)
    x, a = le_a.of(LessEqual)
    S[x], b = le_b.of(LessEqual)
    return Equivalent(et, x <= Min(a, b), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(And(x <= y, x <= b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.le.le.imply.le.min.rhs)

    Eq << Eq[-1].this.lhs.apply(algebra.le.le.given.le.min)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
