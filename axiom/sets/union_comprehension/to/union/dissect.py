from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.dissect import dissect


@apply
def apply(self, indices, wrt=None, *, simplify=True):
    assert self.is_UNION
    return Equal(self, dissect(self, indices, wrt=wrt, simplify=simplify))

 
@prove
def prove(Eq): 
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(UNION[x:A](f(x)), B)
    
    Eq << sets.eq.given.sufficient.apply(Eq[0], wrt='y')
    
    Eq << Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union)
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.ou.split.union)

    
if __name__ == '__main__':
    prove()

