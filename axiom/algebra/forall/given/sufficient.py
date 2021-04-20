from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fn1, *limits = axiom.is_ForAll(given)
    return Sufficient(given.limits_cond.simplify(), fn1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(ForAll[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))
    
    Eq << Eq[1].this.apply(algebra.sufficient.to.forall, wrt=n)

        
if __name__ == '__main__':
    prove()
