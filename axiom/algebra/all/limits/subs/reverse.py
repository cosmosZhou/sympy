from util import *


@apply(given=None)
def apply(self, old, new):
    from axiom.algebra.sum.limits.subs.negate import limits_subs
    return Equivalent(self, limits_subs(All, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i)), i, c - i)

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.all.limits.subs.reverse, i, c - i)
    Eq << Eq[-1].this.rhs.apply(algebra.all.imply.all.limits.subs.reverse, i, c - i)


if __name__ == '__main__':
    run()
