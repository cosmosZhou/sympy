from util import *


@apply
def apply(given, *limits):
    import axiom
    lhs, rhs = given.of(Greater)
    n, a, b = axiom.limit_is_Interval(limits, integer=True)
    assert a >= 0 and b > a + 1 or a > 0 and b > a

    return Greater(Sum(n * lhs, *limits).simplify(), Sum(n * rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(Greater(f(i), g(i)), (i, 0, n + 1))

    k = Symbol.k(domain=Range(1, n + 1))

    Eq << Eq[0].subs(i, k)

    Eq << Eq[-1] * k

    Eq << Eq[-1].apply(algebra.gt.imply.gt.sum, (k,))

    Eq << Eq[-1].this.lhs.limits_subs(k, i)

    Eq << Eq[-1].this.rhs.limits_subs(k, i)


if __name__ == '__main__':
    run()

