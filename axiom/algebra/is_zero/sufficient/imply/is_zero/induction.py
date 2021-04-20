from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given, n=None):
    assert n.is_given == False
    
    f0, sufficient = given
    axiom.is_zero(f0)
    fn, fn1 = axiom.is_Sufficient(sufficient)
    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=False)    
    f = Symbol.f(integer=True, shape=(oo,))
    Eq << apply(Equal(f[0], 0), Sufficient(Equal(f[n], 0), Equal(f[n + 1], 0)), n=n)
    
    g = Symbol.g(LAMBDA[n](KroneckerDelta(f[n], 0)))
    
    Eq << g[0].this.definition
    
    Eq << Eq[-1].this.rhs.subs(Eq[0])
    
    Eq.is_nonzero = algebra.eq.imply.is_nonzero.apply(Eq[-1])

    Eq.sufficient = Sufficient(Unequal(g[n], 0), Unequal(g[n + 1], 0), plausible=True)

    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.reversed
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.reversed
    
    Eq << algebra.is_nonzero.sufficient.imply.is_nonzero.induction.apply(Eq.is_nonzero, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].reversed

        
if __name__ == '__main__':
    prove()
