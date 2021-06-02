from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)
    assert lhs.is_positive

    return Less(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)

    Eq << apply(Less(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq << algebra.all_lt.imply.lt.product.apply(Eq[-1])


if __name__ == '__main__':
    run()

