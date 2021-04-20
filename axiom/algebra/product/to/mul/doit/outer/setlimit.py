from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.doit.outer.setlimit import doit


@apply
def apply(self):
    assert self.is_Product
    return Equal(self, doit(self))


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    
    n = 5
    finiteset = {i for i in range(n)}
    
    Eq << apply(Product[j:f(i), i:finiteset](x[i, j]))
    
    s = Symbol.s(LAMBDA[i](Product[j:f(i)](x[i, j])))
    
    Eq << s[i].this.definition
    
    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, finiteset))
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    prove()

