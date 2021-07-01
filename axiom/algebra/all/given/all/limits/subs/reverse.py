from util import *


@apply
def apply(given, old, new):
    expr, (n, a, b) = given.of(All[Tuple])
    assert n.is_integer
    assert old == n
    m = new + n + 1
    assert m == a + b
    return All[n:m - b:m - a](expr._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)

    Eq << apply(All[n:0:m + 1](f(n) > 0), n, m - n)

    Eq << algebra.all.imply.all.limits.subs.reverse.apply(Eq[1], n, m - n)


if __name__ == '__main__':
    run()

