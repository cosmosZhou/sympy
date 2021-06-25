from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(det(lhs), det(rhs))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    m = Symbol.m(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(m, m), integer=True)
    g = Function.g(shape=(m, m), integer=True)

    Eq << apply(Equal(f(i), g(i)))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], det)


if __name__ == '__main__':
    run()

