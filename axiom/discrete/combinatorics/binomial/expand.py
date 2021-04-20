from axiom.utility import prove, apply
from sympy import *
from axiom import discrete, algebra


@apply
def apply(n, k):
    if not n >= 0:
        print('warning, not proved!')
    
    if not k > 0:
        print('warning, not proved!')
    return Equal(Binomial(n, k), n / k * Binomial(n - 1, k - 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    
    k = Symbol.k(integer=True, positive=True)
    
    Eq << apply(n, k)
    
    Eq << algebra.cond.given.sufficient.bisected.apply(Eq[0], cond=Equal(n, 0))
    
    Eq << Eq[-2].this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.imply.is_positive)
    
    Eq << Eq[-1].apply(algebra.sufficient.given.forall)

    n_ = Symbol.n(integer=True, positive=True)        
    Eq << algebra.forall.given.cond.subs.apply(Eq[-1], Eq[-1].variable, n_)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.find(Binomial).definition
    
    Eq << Eq[-1].this.lhs.find(Factorial).apply(discrete.factorial.to.mul)
    
    Eq << Eq[-1].this.find(Pow, Factorial).apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    prove()
