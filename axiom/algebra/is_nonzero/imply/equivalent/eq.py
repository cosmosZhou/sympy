from util import *


@apply
def apply(given, x):
    p = given.of(Unequal[0])
    return Equivalent(Equal(x, 0), Equal(x * p, 0))


@prove
def prove(Eq):
    from axiom import algebra

    p, x = Symbol(complex=True)
    Eq << apply(Unequal(p, 0), x)

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[1])

    Eq << Eq[-2].this.lhs * p

    Eq << Eq[-1].this.lhs / p

    Eq << algebra.cond.given.cond.subs.bool.apply(Eq[-1], given=Eq[0], invert=True)


if __name__ == '__main__':
    run()