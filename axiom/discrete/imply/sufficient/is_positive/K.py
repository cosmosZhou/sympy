from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import K


@apply
def apply(x): 
    i = x.generate_free_symbol(integer=True, free_symbol='i')
    n = x.shape[0]
    return Sufficient(ForAll[i:1:n](x[i] > 0), Greater(K(x), 0))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)
    
    Eq << apply(x[:n])
    
    Eq.initial0 = Eq[-1].subs(n, 1)
    
    Eq << Eq.initial0.this.lhs.definition
        
    Eq.initial1 = Eq[-1].subs(n, 2)
    
    Eq << Eq.initial1.this.find(K).definition
            
    Eq.induct = Eq[0].subs(n, n + 2)
    
    Eq << Eq.induct.this.find(K).definition
    
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

