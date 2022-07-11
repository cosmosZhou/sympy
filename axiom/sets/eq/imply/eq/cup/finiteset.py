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
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.imply.all.apply(Eq[0], i)

    Eq << sets.all_eq.imply.eq.cup.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-24
