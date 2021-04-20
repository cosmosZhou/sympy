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
    
    a_d, n_d = axiom.is_Interval(Si) 
    i_d, n = axiom.is_Interval(Sj)
    
    d = i - i_d
    
    a = a_d - d
    assert n_d == n + d + 1
    
    return Contains(i, Interval(a + d, d + j, integer=True)), Contains(j, Interval(a - 1, n, right_open=True, integer=True)) 


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    
    Eq << apply(Contains(j, Interval(i - d + 1, n, right_open=True, integer=True)), Contains(i, Interval(a + d, d + n, right_open=True, integer=True)))
    
    Eq << sets.contains.imply.contains.interval.sub.apply(Eq[1], d)
    
    Eq << sets.contains.given.contains.interval.subtract.apply(Eq[2], d)
    
    Eq <<= algebra.et.given.cond.apply(sets.contains.given.et.split.interval.apply(Eq[-1])), \
    algebra.et.given.cond.apply(sets.contains.given.et.split.interval.apply(Eq[3]))
    
    Eq <<= algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[0])), \
    algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[4]))
    
    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-2], Eq[7])
    
    Eq << algebra.gt.imply.ge.relax.apply(Eq[-1])
    
    Eq << Eq[-3].reversed


if __name__ == '__main__':
    prove()

