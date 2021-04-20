from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from sympy.concrete.limits import limits_cond


@apply(given=None)
def apply(given, *, simplify=True):
    fn1, *limits = axiom.is_ForAll(given)
    cond = limits_cond(limits)
    if simplify:
        cond = cond.simplify()
    return Equivalent(given, Sufficient(cond, fn1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(ForAll[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))
    
    Eq << algebra.equivalent.given.sufficient.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.forall.imply.sufficient)
    
    Eq << Eq[-1].this.rhs.apply(algebra.forall.given.sufficient)

        
if __name__ == '__main__':
    prove()
