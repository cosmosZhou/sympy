from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


# given e not in S
@apply
def apply(given):
    assert given.is_NotContains
    n, interval = given.args
    a, _n = axiom.is_Interval(interval)
    assert n == _n - 1
    return LessThan(n, a - 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(NotContains(n, Interval(a, n, integer=True)))
    
    Eq << ~Eq[-1]
    
    Eq << algebre.gt.imply.ge.strengthen.apply(Eq[-1])
    
    Eq << sets.ge.imply.contains.apply(Eq[-1], simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

