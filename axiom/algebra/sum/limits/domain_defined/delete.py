from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


def limits_delete(self):
    function, *limits = self.args
    
    * limits, limit = limits   
    x, domain = limit.coerce_setlimit()
    
    assert function.domain_defined(x) in domain    
    return self.func(function, *limits, (x,))
    
@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), integer=True)
    
    f = Function.f(etype=dtype.integer)
    h = Function.h(real=True)
    
    Eq << apply(Sum[j:f(i), i:0:k](h(x[i], j)))
    
    s = Symbol.s(Sum[j:f(i)](h(x[i], j)))
    Eq << s.this.definition
    
    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, k))
    
    Eq << Eq[-1].this.lhs.function.definition
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

