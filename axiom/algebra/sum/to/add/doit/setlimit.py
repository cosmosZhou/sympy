from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


def doit(self):
    xi, *limits = self.args
    i, s = axiom.limit_is_set(limits)
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    while s:
        t, *args = s.args        
        sgm = self.func.operator(sgm, xi._subs(i, t))
        
        s = FiniteSet(*args)
        assert Contains(t, s).is_BooleanFalse
        
    return sgm

    
@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, doit(self))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    
    n = 5
    finiteset = {i for i in range(n)}
    
    Eq << apply(Sum[i:finiteset](x[i]))
    
    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, {n})


if __name__ == '__main__':
    prove()

