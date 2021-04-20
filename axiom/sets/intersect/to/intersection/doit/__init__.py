from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
from axiom.algebra.sum.to.add.doit import doit


@apply
def apply(self):
    assert self.is_INTERSECTION
    return Equal(self, doit(self))

 
@prove
def prove(Eq):
    n = 5
    x = Symbol.x(etype=dtype.real, shape=(n,))    
    i = Symbol.i(integer=True)

    Eq << apply(INTERSECTION[i](x[i]))
    
    Eq << Eq[-1].this.lhs.apply(sets.intersect.limits.domain_defined.insert)
    
    n -= 1
    Eq << Eq[-1].this.lhs.apply(sets.intersect.to.intersection.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].rhs.find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n})
    
    n -= 1
    Eq << Eq[-1].rhs.find(INTERSECTION).this.apply(sets.intersect.to.intersection.dissect, {n})

    Eq << Eq[4].subs(Eq[-1])
    
    Eq << Eq[3].subs(Eq[-1])
    
    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    prove()

from . import outer
from . import setlimit
