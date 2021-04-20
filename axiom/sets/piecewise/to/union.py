from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    (s, et), (emptyset, _) = axiom.is_Piecewise(self)
    assert emptyset.is_UniversalSet
    
    eqs = axiom.is_And(et) 
    
    return Equal(self, Union(*(Piecewise((s, eq), (s.etype.universalSet, True)) for eq in eqs)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    s = Function.s(etype=dtype.complex * n)
    
    x = Symbol.x(complex=True, shape=(n,))
    
    f = Function.f(integer=True, shape=())
    g = Function.g(integer=True, shape=())
     
    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.universalSet, True)))
    
    t = Symbol.t(complex=True, shape=(n,))
    Eq.sufficient, Eq.necessary = sets.eq.given.sufficient.apply(Eq[0], wrt=t)
    
    Eq << Eq.sufficient.this.find(Contains).apply(sets.contains.imply.ou.st.piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebra.ou.to.sufficient, index=Slice[1:3])
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.given.ou.split.union, simplify=None)
    
    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.given.ou.st.piecewise)
    
    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.given.ou.st.piecewise)
    
    Eq << Eq[-1].this.rhs.apply(algebra.ou.to.sufficient, index=Slice[2:4])
    
    Eq << Eq.necessary.this.find(Contains).apply(sets.contains.imply.ou.split.union, simplify=None)
        
    Eq << Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.ou.st.piecewise)
    
    Eq << Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.ou.st.piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebra.ou.to.sufficient, index=Slice[2:4])
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.given.ou.st.piecewise)
    
    Eq << Eq[-1].this.rhs.apply(algebra.ou.to.sufficient, index=Slice[1:3])
    
    
if __name__ == '__main__':
    prove()


