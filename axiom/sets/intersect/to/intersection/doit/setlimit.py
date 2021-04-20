from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.doit.setlimit import doit


@apply
def apply(self):
    assert self.is_INTERSECTION
    return Equal(self, doit(self))


@prove
def prove(Eq):
    x = Symbol.x(etype=dtype.real, shape=(oo,))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    
    n = 5
    finiteset = {i for i in range(n)}
    
    Eq << apply(INTERSECTION[i:finiteset](x[i]))
    
    n -= 1
    Eq << Eq[-1].lhs.this.apply(sets.intersect.to.intersection.dissect, {n}, simplify=False)
    
    Eq << Eq[-1].this.rhs.find(INTERSECTION).simplify()
    
    n -= 1
    Eq << Eq[-1].rhs.find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n}, simplify=False)
    Eq << Eq[-1].this.rhs.find(INTERSECTION).simplify()
    
    n -= 1
    Eq << Eq[-1].rhs.find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n}, simplify=False)
    Eq << Eq[-1].this.rhs.find(INTERSECTION).simplify()
    
    n -= 1
    Eq << Eq[-1].rhs.find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n}, simplify=False)
    Eq << Eq[-1].this.rhs.find(INTERSECTION).simplify()
    Eq << Eq[-1].this.rhs.find(INTERSECTION).simplify()
    
    Eq << Eq[6].subs(Eq[-1])
    
    Eq << Eq[4].subs(Eq[-1])
    
    Eq << Eq[2].subs(Eq[-1])
    


if __name__ == '__main__':
    prove()

