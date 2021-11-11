from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    assert rhs.is_nonnegative

    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True, nonnegative=True)

    Eq << apply(All[i:n](f(i) >= g(i)))

    Eq << algebra.imply.infer.ge.induct.prod.apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-01-12
# updated on 2019-01-12
