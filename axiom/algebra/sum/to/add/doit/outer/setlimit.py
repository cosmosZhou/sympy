from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


def doit(self):
    xi, *limits = self.args
    * limits, limit = limits
    assert limits
    i, s = axiom.limit_is_set((limit,))
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    while s:
        t, *args = s.args
        
        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, t) for c in ab)))
            
        sgm = self.func.operator(sgm, self.func(xi._subs(i, t), *_limits))
        
        s = FiniteSet(*args)
        assert Contains(t, s).is_BooleanFalse
        
    return sgm
    
@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, doit(self))


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    
    n = 5
    finiteset = {i for i in range(n)}
    
    Eq << apply(Sum[j:f(i), i:finiteset](x[i, j]))
    
    s = Symbol.s(LAMBDA[i](Sum[j:f(i)](x[i, j])))
    
    Eq << s[i].this.definition
    
    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, finiteset))
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    prove()

