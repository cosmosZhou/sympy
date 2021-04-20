from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, function):
    et_j, et_i = axiom.is_Equivalent(given)
    Aj_contains_j, Ai_contains_i = axiom.is_And(et_j)
    j, Aj = axiom.is_Contains(Aj_contains_j)
    i, Ai = axiom.is_Contains(Ai_contains_i)
    
    Bi_contains_i, Bj_contains_j = axiom.is_And(et_i)
    _i, Bi = axiom.is_Contains(Bi_contains_i)
    _j, Bj = axiom.is_Contains(Bj_contains_j)
    
    if i != _i:
        _i, Bi, _j, Bj = _j, Bj, _i, Bi   

    assert _i == i        
    assert _j == j
    
    assert not Aj._has(i)
    assert not Bi._has(j)
    return Equal(Sum[i:Ai, j:Aj](function), Sum[j:Bj, i:Bi](function))


@prove
def prove(Eq): 
    i = Symbol.i(integer=True)    
    j = Symbol.j(integer=True)
    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    f = Function.f(etype=dtype.integer)
    g = Function.g(etype=dtype.integer)
    h = Function.h(complex=True)
    
    Eq << apply(Equivalent(Contains(i, A) & Contains(j, f(i)), Contains(j, B) & Contains(i, g(j))), h(i, j))
        
    Eq << Eq[1].this.lhs.apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap)

    Eq << algebra.equivalent.imply.eq.subs.apply(Eq[0], Eq[-1].lhs)

    
if __name__ == '__main__':
    prove()

from . import collapse