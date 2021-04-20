from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(given=None)
def apply(given):
    contains_i, contains_j = axiom.is_And(given)
    i, Si = axiom.is_Contains(contains_i)
    j, Sj = axiom.is_Contains(contains_j)
    
    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)
    
    a_d, d_j = axiom.is_Interval(Si) 
    a, n_d = axiom.is_Interval(Sj)
    
    d = d_j - j
    a -= 1
    assert d == a_d - a    
    
    return Equivalent(given, And(Contains(i, Interval(a + d, n_d - 1 + d, right_open=True, integer=True)), Contains(j, Interval(i - d + 1, n_d - 1, integer=True))))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(And(Contains(i, Interval(a + d, j - 1 + d, integer=True)), Contains(j, Interval(a + 1, n - 1, integer=True))))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(sets.contains.contains.imply.contains.interval.i_lt_j.i_in_j)
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.contains.imply.contains.interval.i_lt_j.j_in_i)

    
if __name__ == '__main__':
    prove()

from . import left_close