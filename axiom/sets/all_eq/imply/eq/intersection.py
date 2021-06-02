from util import *



@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Equal])

    return Equal(Cap(lhs, *limits).simplify(), Cap(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)

    Eq << apply(ForAll[i:n](Equal(f(i), g(i))))

    Eq << sets.imply.suffice.eq.intersection.induct.apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

