from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(given=None)
def apply(given):
    contains_i, contains_j = axiom.is_And(given)     
    i, Si = axiom.is_Contains(contains_i)
    j, Sj = axiom.is_Contains(contains_j)
    
    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)
    
    d_j, n = axiom.is_Interval(Si) 
    a, n_d = axiom.is_Interval(Sj)
    
    d = n - n_d
    assert d_j == j + d
    
    return Equivalent(given, And(Contains(j, Interval(a, i - d, integer=True)), Contains(i, Interval(a + d, n - 1, integer=True))))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Contains(i, Interval(d + j, n-1, integer=True)) & Contains(j, Interval(a, n-d-1, integer=True)))
    
    Eq << Sufficient(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.contains.imply.et.i_in_j)
    
    Eq << Necessary(*Eq[0].args, plausible=True)

    Eq << Eq[-1].this.rhs.apply(sets.contains.contains.imply.et.j_in_i)
    
    Eq <<= Eq[2] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

