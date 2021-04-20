from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import K


@apply
def apply(x): 
    i = x.generate_free_symbol(integer=True, free_symbol='i')
    n = x.shape[0]
    assert n >= 2
    return Sufficient(ForAll[i:1:n](x[i] >= 1), GreaterEqual(K(x), K(x[:n - 1])))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(x[:n + 1])
    
    Eq.initial1 = Eq[-1].subs(n, 1)
    
    Eq << Eq.initial1.this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
        
    Eq.initial2 = Eq[0].subs(n, 2)
    
    Eq << Eq.initial2.this.lhs.doit()
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.lhs.args[1] - 1
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_nonnegative.ge.imply.ge.mul)
    
    Eq << Eq[-1].this.lhs.lhs.expand()
    
    Eq << Eq[-1].this.rhs - (x[1] + 1)
    
    Eq << algebra.sufficient.given.ou.apply(Eq[-1])
        
    Eq.case2, Eq.case1 = algebra.cond.given.sufficient.bisected.apply(Eq[0], cond=n >= 2)
    
    Eq << Eq.case1.this.lhs.apply(algebra.lt.to.eq.squeeze)
    
    Eq << Eq[-1].this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    return
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.find(K).definition
    return
    Eq.hypothesis = Eq[0].subs(n, n + 1)
    
    Eq << Eq.hypothesis.this.lhs.apply(algebra.forall.given.forall.limits.relaxed, Interval(1, n + 1))
    
    Eq << algebra.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << Eq[-1].this.find(And, ForAll).apply(algebra.forall.imply.cond.subs, Eq[-1].lhs.variable, n + 1)
    
    Eq << Eq[-1].this.find(And).apply(algebra.is_positive.is_positive.imply.is_positive.mul)
    
    Eq << Eq[0].this.lhs.apply(algebra.forall.given.forall.limits.relaxed, Interval(1, n + 1))
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].this.find(And).apply(algebra.is_positive.is_positive.imply.is_positive.add)
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.cond.sufficient.imply.cond.induction.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)
    
    Eq << Eq[0].subs(n, n + 1)
    
    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    prove()

