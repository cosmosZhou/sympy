from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, function):
    et_j, et_i = axiom.is_Equivalent(given)
    Aj_contains_j, Ai_contains_i = axiom.is_And(et_j)
    j, Aj = axiom.is_Contains(Aj_contains_j)
    i, Ai = axiom.is_Contains(Ai_contains_i)
    
    Bi_eq_i, Bj_contains_j = axiom.is_And(et_i)
    if not Bi_eq_i.is_Equal:
        Bi_eq_i, Bj_contains_j = Bj_contains_j, Bi_eq_i
        
    _i, Bi = axiom.is_Equal(Bi_eq_i)
    _j, Bj = axiom.is_Contains(Bj_contains_j)
    
    if i != _i:
        _i, Bi, _j, Bj = _j, Bj, _i, Bi   

    assert _i == i        
    assert _j == j
    
    assert not Aj._has(i)
    assert not Bi._has(j)
    return Equal(Sum[i:Ai, j:Aj](function), Sum[i:Bi](function._subs(j, Bj)))


@prove
def prove(Eq): 
    i = Symbol.i(integer=True)    
    j = Symbol.j(integer=True)
    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    f = Function.f(etype=dtype.integer)
    g = Function.g()
    h = Function.h(complex=True)
    
    Eq << apply(Equivalent(Contains(i, A) & Contains(j, f(i)), Contains(j, B) & Equal(i, g(j))), h(i, j))
    
    Eq << Eq[0].this.find(Equal).apply(sets.eq.to.contains)
    
    Eq << algebra.equivalent.imply.eq.sum.apply(Eq[-1], h(i, j))
    
    Eq << Eq[-1].this.rhs. apply(algebra.sum.simplify.conditionset)

    
if __name__ == '__main__':
    prove()

