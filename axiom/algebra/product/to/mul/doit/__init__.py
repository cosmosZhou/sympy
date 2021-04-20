from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.doit import doit


@apply
def apply(self):
    assert self.is_Product
    return Equal(self, doit(self))

 
@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = 5
    x = Symbol.x(real=True, shape=(n, k))    
    i = Symbol.i(integer=True)
     
    
    Eq << apply(Product[i](x[i]))
    
    Eq << Eq[-1].this.lhs.apply(algebra.product.limits.domain_defined.insert)
    
    n -= 1
    Eq << Eq[-1].this.lhs.bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.find(Product).bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.find(Product).bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.find(Product).bisect({n})


if __name__ == '__main__':
    prove()

from . import outer
from . import setlimit
