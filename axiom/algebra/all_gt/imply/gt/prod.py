from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])
    assert rhs.is_positive

    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True, positive=True)

    Eq << apply(All[i:n](f(i) > g(i)))

    Eq << algebra.imply.suffice.gt.induct.prod.apply(f(i) > g(i), (i, 0, n))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

