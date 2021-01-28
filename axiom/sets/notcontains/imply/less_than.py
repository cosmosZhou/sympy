from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


# given e not in S
@apply(imply=True)
def apply(given):
    assert given.is_NotContains
    n, interval = given.args
    a, _n = axiom.is_Interval(interval, end=None)
    assert n == _n - 1
    return LessThan(n, a - 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(NotContains(n, Interval(a, n, integer=True)))
    
    Eq << ~Eq[-1]
    
    Eq << algebre.strict_greater_than.imply.greater_than.rewrite.apply(Eq[-1])
    
    Eq << sets.greater_than.imply.contains.apply(Eq[-1], simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

