from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import K


@apply
def apply(x, n): 
    return ForAll[x[:n]:CartesianSpace(Interval(1, oo, integer=True), n)](Greater(K(x[:n]), 0))


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)
    
    Eq << apply(x, n)
    
    Eq.initial0 = Eq[-1].subs(n, 1)
    
    Eq << Eq.initial0.this.function.lhs.definition
        
    Eq.initial1 = Eq[-1].subs(n, 2)
    
    Eq << Eq.initial1.this.function.lhs.definition
    
    Eq << algebra.forall.given.forall.limits.split.apply(Eq[-1], index=1)
    
    Eq << algebra.forall.given.ou.apply(Eq[-1])            
            
    Eq.induct = Eq[0].subs(n, n + 2)
    
    Eq << Eq.induct.this.function.lhs.definition
    
    Eq << Eq[0].this.function.apply(algebra.cond.imply.forall.restrict, (x[n:n + 2], CartesianSpace(Interval(1, oo, integer=True), 2)), simplify=None)
    Eq.is_positive = algebra.forall.imply.forall.limits.merge.apply(Eq[-1])    
    
    Eq.hypothesis = Eq[0].subs(n, n + 1)
    
    Eq << Eq.hypothesis.this.function.apply(algebra.cond.imply.forall.restrict, (x[n + 1], 1, oo), simplify=None)
    
    Eq << algebra.forall.imply.forall_et.apply(Eq[-1], index=0, simplify=None)
    
    Eq << algebra.forall.imply.forall.limits.merge.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.args[1].apply(sets.contains.imply.ge.split.interval)
    
    Eq << Eq[-1].this.function.args[1].apply(algebra.ge.imply.gt.transit, 0)
    
    Eq << Eq[-1].this.function.apply(algebra.is_positive.is_positive.imply.is_positive.mul)
    
    Eq <<= Eq.is_positive & Eq[-1]
    
    Eq << Eq[-1].this.function.apply(algebra.is_positive.is_positive.imply.is_positive.add)
    
    Eq << Eq.induct.induct()

    Eq << algebra.cond.cond.sufficient.imply.cond.induction.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)
    
    Eq << Eq[0].subs(n, n + 1)
    
    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    prove()

