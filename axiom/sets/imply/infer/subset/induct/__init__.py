from util import *


@apply(given=None)
def apply(given, limit):
    fk, gk = given.of(Subset)
    k, a, b = limit

    return Infer(All[k:a:b](Subset(fk, gk)), Subset(Cup[k:a:b](fk), Cup[k:a:b](gk)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(Subset(f(k), g(k)), (k, 0, n))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[0], cond=Subset(f(n), g(n)))

    Eq << Eq[-1].this.rhs.apply(sets.subset.subset.imply.subset.cup.push_back)

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import lhs
# created on 2020-08-02
