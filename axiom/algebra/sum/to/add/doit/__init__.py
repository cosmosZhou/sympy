from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


def doit(self):
    xi, *limits = self.args
    try:
        i, a, b = axiom.limit_is_Interval(limits)
    except:
        i = axiom.limit_is_symbol(limits)
        domain = xi.domain_defined(i)
        a, b = axiom.is_Interval(domain)
    
    diff = b - a
    assert diff == int(diff)

    sgm = self.func.identity(xi)
    for t in range(diff): 
        sgm = self.func.operator(sgm, xi._subs(i, a + t))
        
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
     
    n = 5
    Eq << apply(Sum[i:n](x[i]))
    
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
