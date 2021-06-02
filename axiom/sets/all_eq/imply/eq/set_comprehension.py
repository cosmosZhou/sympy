from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Equal])

    return Equal(Cup(FiniteSet(lhs), *limits).simplify(), Cup(FiniteSet(rhs), *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Symbol.f(shape=(oo,), etype=dtype.integer)
    g = Symbol.g(shape=(oo,), etype=dtype.integer)

    Eq << apply(ForAll[i:n](Equal(f[i], g[i])))

    Eq << Eq[0].this.function.apply(sets.eq.imply.eq.set, simplify=False)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

