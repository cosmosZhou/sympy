from util import *


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)
    lhs, rhs = Cup(lhs.set, *limits), Cup(rhs.set, *limits)
    if simplify:
        lhs, rhs = lhs.simplify(), rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].forall((i,))

    Eq << sets.all_eq.imply.eq.set_comprehension.apply(Eq[-1])


if __name__ == '__main__':
    run()

