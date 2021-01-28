from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply(imply=True)
def apply(contains_i, contains_j):
    i, Si = axiom.is_Contains(contains_i)
    j, Sj = axiom.is_Contains(contains_j)
    
    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)
    
    d_j, n = axiom.is_Interval(Si, end=None) 
    a, n_d = axiom.is_Interval(Sj, end=None)
    
    d = n - n_d
    assert d_j == j + d
    
    return And(Contains(j, Interval(a, i - d, integer=True)), Contains(i, Interval(a + d, n - 1, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    
    Eq << apply(Contains(i, Interval(d + j, n-1, integer=True)), Contains(j, Interval(a, n-d-1, integer=True)))
    
    Eq << Eq[-1].split()
    
    Eq <<= Eq[-2].split(), Eq[-1].split()
    
    Eq <<= Eq[0].split(), Eq[1].split()
    
    Eq << Eq[-2] - d
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[-1], Eq[-5]) + d
    
    Eq << Eq[-1].reversed
    
    
    


if __name__ == '__main__':
    prove(__file__)

