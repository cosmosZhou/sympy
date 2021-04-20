from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(contains_j, contains_i):
    j, Sj = axiom.is_Contains(contains_j)
    i, Si = axiom.is_Contains(contains_i)
    
    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)
    
    a_d, n = axiom.is_Interval(Si) 
    a, i_d = axiom.is_Interval(Sj)
    
    d = i - i_d + 1
    assert a_d == a + d
    
    return Contains(i, Interval(d + j, n - 1, integer=True)), Contains(j, Interval(a, n - d - 1, integer=True)) 


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    
    Eq << apply(Contains(j, Interval(a, i - d, integer=True)), Contains(i, Interval(a + d, n - 1, integer=True)))
    
    Eq <<= algebra.et.given.cond.apply(sets.contains.given.et.split.interval.apply(Eq[-2])), \
    algebra.et.given.cond.apply(sets.contains.given.et.split.interval.apply(Eq[-1]))
    
    Eq <<= algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[0])), \
    algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[1]))
    
    Eq << Eq[-2] + d
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[4]) - d
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

