from util import *



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Cap(lhs, *limits).simplify(), Cap(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.imply.all.apply(Eq[0], i)

    Eq << sets.all_eq.imply.eq.intersection.apply(Eq[-1])


if __name__ == '__main__':
    run()

