from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(contains_i, contains_j):
    i, Si = axiom.is_Contains(contains_i)
    j, Sj = axiom.is_Contains(contains_j)
    
    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)
    
    a_d, d_j = axiom.is_Interval(Si) 
    a, n_d = axiom.is_Interval(Sj)
    
    d = d_j - j
    
    assert d == a_d - a
    
    return Contains(i, Interval(a + d, n_d + d, right_open=True, integer=True)), Contains(j, Interval(i - d + 1, n_d - 1, integer=True))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    
    Eq << apply(Contains(i, Interval(a + d, j - 1 + d, integer=True)), Contains(j, Interval(a, n - 1, integer=True)))
    
    Eq << sets.contains.imply.contains.interval.sub.apply(Eq[0], d)
    
    Eq << sets.contains.given.contains.interval.subtract.apply(Eq[2], d)
    
    Eq <<= sets.contains.given.et.split.interval.apply(Eq[3]), sets.contains.given.et.split.interval.apply(Eq[-1])
    
    Eq <<= algebra.et.given.cond.apply(Eq[-2]), algebra.et.given.cond.apply(Eq[-1])
    
    Eq <<= algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[4])), algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[1]))
    
    Eq << Eq[-2].reversed
    
    Eq << algebra.lt.lt.imply.lt.transit.apply(Eq[-2], Eq[8])
    

if __name__ == '__main__':
    prove()

