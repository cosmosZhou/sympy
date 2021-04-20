from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.doit.inner import doit

    
@apply
def apply(self):
    assert self.is_Product
    return Equal(self, doit(self))


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    
    n = 5
    Eq << apply(Product[j:n, i:m](x[i, j]))
    
    s = Symbol.s(LAMBDA[i](Product[j:n](x[i, j])))
    
    Eq << s[i].this.definition
    
    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, 0, m))
    
    Eq << Eq[-2].this.rhs.apply(algebra.product.to.mul.doit)
    
    Eq << Eq[-2].subs(Eq[-1]).reversed

    
if __name__ == '__main__':
    prove()

