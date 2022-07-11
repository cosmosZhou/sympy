from util import *



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.imply.all.apply(Eq[0], i)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-28
from . import finiteset
