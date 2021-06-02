from util import *

import axiom


@apply(given=None)
def apply(given, *limits):
    fk, gk = given.of(Subset)
    k, a, b = axiom.limit_is_Interval(limits)

    return Suffice(ForAll[k:a:b](Subset(fk, gk)), Subset(Cup[k:a:b](fk), Cup[k:a:b](gk)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)

    Eq << apply(Subset(f(k), g(k)), (k, 0, n))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=Subset(f(n), g(n)))

    Eq << Eq[-1].this.rhs.apply(sets.subset.subset.imply.subset.cup.absorb.back)

    Eq << Eq[-1].this.lhs.apply(algebra.et.given.all.absorb.back)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import lhs
