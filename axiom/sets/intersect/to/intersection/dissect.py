from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.dissect import dissect

@apply
def apply(self, indices, wrt=None, *, simplify=True):
    assert self.is_INTERSECTION
    return Equal(self, dissect(self, indices, wrt=wrt, simplify=simplify))

 
@prove
def prove(Eq):        
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(INTERSECTION[x:A](f(x)), B)
    
    Eq << sets.eq.given.sufficient.apply(Eq[0], wrt='y')
    
    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection),\
    Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection)
    
    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.forall_contains.st.intersect),\
    Eq[-1].this.rhs.apply(sets.contains.given.forall_contains.st.intersect)
    
    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.forall_contains.st.intersect),\
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.forall_contains.st.intersect)
    
    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.forall_contains.st.intersect),\
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.forall_contains.st.intersect)
    
    Eq <<= Eq[-2].this.rhs.apply(algebra.et.given.forall.limits_union),\
    Eq[-1].this.lhs.apply(algebra.forall.forall.imply.forall.limits_union)
    
if __name__ == '__main__':
    prove()

