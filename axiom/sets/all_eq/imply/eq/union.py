from util import *



@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(All[i:n](Equal(f(i), g(i))))

    Eq << sets.imply.infer.eq.cup.induct.apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-27
