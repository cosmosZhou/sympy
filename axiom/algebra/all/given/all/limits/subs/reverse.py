from util import *

import axiom


@apply
def apply(given, old, new):
    function, *limits = given.of(ForAll)
    assert given.is_ForAll
    n, a, b = axiom.limit_is_Interval(limits, integer=True)
    assert old == n
    m = new + n + 1
    assert m == a + b
    return ForAll[n:m - b:m - a](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)

    Eq << apply(ForAll[n:0:m + 1](f(n) > 0), n, m - n)

    Eq << algebra.all.imply.all.limits.subs.reverse.apply(Eq[1], n, m - n)


if __name__ == '__main__':
    run()

