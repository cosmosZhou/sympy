from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
from axiom.algebra.sum.limits.domain_defined.delete import limits_delete


@apply
def apply(self):
    assert self.is_Product
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), integer=True)
    
    f = Function.f(etype=dtype.integer)
    h = Function.h(real=True)
    
    Eq << apply(Product[j:f(i), i:0:k](h(x[i], j)))
    
    s = Symbol.s(Product[j:f(i)](h(x[i], j)))
    Eq << s.this.definition
    
    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, 0, k), simplify=False)
    
    Eq << Eq[-1].this.lhs.function.definition
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

