from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Subset])
    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(All[i:n](Subset(f(i), g(i))))

    Eq << sets.imply.suffice.subset.induct.apply(Subset(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

from . import lhs
