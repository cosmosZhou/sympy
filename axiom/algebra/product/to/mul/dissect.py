from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.dissect import dissect


@apply
def apply(self, indices, wrt=None, *, simplify=True):
    assert self.is_Product
    return Equal(self, dissect(self, indices, wrt=wrt, simplify=simplify), evaluate=False)

 
@prove
def prove(Eq): 
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Product[x:A](f(x)), B)
    
    Eq << Eq[-1].this.find(Product).apply(algebra.product.bool)
    
    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.product.bool)
    
    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.product.bool)
    
    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.product)
    
    Eq << Eq[-1].this.rhs.function.powsimp()

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.to.ou.dissect, B)
    
    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.add)


if __name__ == '__main__':
    prove()

