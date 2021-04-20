from axiom.utility import prove, apply
from sympy import *
from axiom import algebra, sets
import axiom


@apply
def apply(given, old, new):
    function, *limits = axiom.is_ForAll(given)
    assert given.is_ForAll
    n, a, b = axiom.limit_is_Interval(limits, integer=True)
    assert old == n
    m = new + n + 1
    assert m == a + b
    return ForAll[n:m - b:m - a](function._subs(old, new))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)

    Eq << apply(ForAll[n:0:m + 1](f(n) > 0), n, m - n)
    
    Eq << algebra.forall.imply.forall.limits.subs.reverse.apply(Eq[1], n, m - n)


if __name__ == '__main__':
    prove()

