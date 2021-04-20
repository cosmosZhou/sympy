from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.doit.outer import doit


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
    Eq << apply(Product[j:f(i), i:n](x[i, j]))
    
    s = Symbol.s(LAMBDA[i](Product[j:f(i)](x[i, j])))
    
    Eq << s[i].this.definition
    
    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, 0, n))
    
    Eq << Eq[-1].this.lhs.apply(algebra.product.to.mul.doit).reversed
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition
    
    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    prove()

from . import setlimit