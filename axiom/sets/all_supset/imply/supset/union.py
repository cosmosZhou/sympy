from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Supset])
    return Supset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)

    Eq << apply(ForAll[i:n](Supset(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

