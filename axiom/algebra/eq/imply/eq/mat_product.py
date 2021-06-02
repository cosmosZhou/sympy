from util import *
import axiom



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(MatProduct(lhs, *limits).simplify(), MatProduct(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].forall((i,))

    Eq << algebra.all_eq.imply.eq.mat_product.apply(Eq[-1])


if __name__ == '__main__':
    run()
