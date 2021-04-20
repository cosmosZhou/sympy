from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)
    
    limit, *limits = limits   
    x, condset = limit
    _x, condition, base_set = axiom.is_ConditionSet(condset)
    assert x == _x
    assert base_set.is_UniversalSet
    
    _x, fx = axiom.is_Equal(condition)
    assert x == _x
    function = function._subs(x, fx)
    
    return Equal(self, self.func(function, *limits))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    C = Symbol.C(etype=dtype.integer, given=True)
    
    f = Function.f(integer=True)
    h = Function.h(real=True)
    
    Eq << apply(Sum[j:conditionset(j, Equal(j, f(i))), i:C](h(i, j)))
    
    Eq << Sum[j:conditionset(j, Equal(j, f(i)))](h(i, j)).this.simplify()
    
    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.find(Bool).definition
    
    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, C))
    
    

if __name__ == '__main__':
    prove()

