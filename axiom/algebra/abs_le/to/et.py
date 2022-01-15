from util import *


@apply(given=None)
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    return Equivalent(le, And(LessEqual(x, a), GreaterEqual(x, -a)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.abs_le.imply.et)

    Eq << Eq[-1].this.lhs.apply(algebra.abs_le.given.et)

    


if __name__ == '__main__':
    run()
# created on 2022-01-07
