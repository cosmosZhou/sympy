from util import *
import axiom


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[LessEqual])
    assert lhs.is_nonnegative

    return LessEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, nonnegative=True)
    g = Function.g(shape=(), real=True, nonnegative=True)

    Eq << apply(ForAll[i:n](LessEqual(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << algebra.all_ge.imply.ge.product.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

