from util import *


@apply(given=None)
def apply(self, old, new):
    from axiom.algebra.sum.limits.subs.negate import limits_subs
    return Equivalent(self, limits_subs(Any, self, old, new), evaluate=False)


@prove(proved=False)
def prove(Eq):
    from axiom import algebra, sets

    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    f = Function.f(real=True)
    Eq << apply(Any[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(algebra.product.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.product.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.negate)

    Eq << Eq[-1].this.rhs.limits_subs(i, i - c)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.add, c)

    Eq << Eq[-1].this.lhs.apply(algebra.product.bool)


if __name__ == '__main__':
    run()
from . import real
