from util import *

import axiom

from axiom.algebra.sum.to.add import associate


@apply
def apply(self, simplify=True):
    assert self.is_Product
    return Equal(self, associate(self, simplify=simplify))


@prove(provable=False)
def prove(Eq): 
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    
    f = Function.f(real=True)
    h = Function.h(real=True)
    
    Eq << apply(Product[i:n](f(i) * h(i)))
    
    Eq << Eq[0].subs(n, 1)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    # this will cause a cyclic proof
    return
    Eq << Eq.induct.this.lhs.apply(algebra.product.to.mul.dissect, cond={n})
    
    Eq << Eq[-1].this.lhs.apply(algebra.mul.flatten)
    
    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.product.to.mul.dissect, cond={n})
    
    Eq << Eq[-1].this.find(Product[2]).apply(algebra.product.to.mul.dissect, cond={n})
    
    Eq << Eq[0] * Mul(*Eq[-1].lhs.args[:2])
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()    
    

from . import st
from . import doit
from . import dissect
from . import push_front
from . import push_back
