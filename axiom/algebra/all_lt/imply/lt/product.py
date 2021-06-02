from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Less])
    assert lhs.is_positive

    return Less(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)

    Eq << apply(ForAll[i:n](Less(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << algebra.all_gt.imply.gt.product.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

