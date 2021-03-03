from sympy import *
from axiom.utility import prove, apply
import axiom

from axiom import algebre


@apply
def apply(A, B, n=None, k=None, x=None):
    
    if x is None:
        x = Symbol.x(real=True)
    
    if n is None:
        n = Symbol.n(integer=True)
    if k is None:
        k = Symbol.k(integer=True)
        
    return Equality(Sum[n:0:oo](A[n] * x ** n) * Sum[n:0:oo](B[n] * x ** n), Sum[n:0:oo](Sum[k:0:n + 1](A[n - k] * B[k]) * x ** n))


@prove
def prove(Eq):
    A = Symbol.A(shape=(oo,), real=True)
    B = Symbol.B(shape=(oo,), real=True)
    Eq << apply(A, B)
    
    Eq << Eq[0].lhs.this.astype(Sum)
    
    Eq << Eq[-1].this.rhs.function.astype(Sum)
    
    i, n = Eq[-1].rhs.variables    
    k = Eq[0].rhs.function.args[1].variable
    
    Eq << Eq[-1].this.rhs.limits_subs(i, k)
    
    Eq << Eq[-1].this.rhs.limits_swap()
    
    Eq << Eq[-1].this.rhs.limits_subs(n, n - k)
        
    Eq << Eq[-1].this.rhs.apply(algebre.sum.limits_swap)
    
    Eq << Eq[-1].this.rhs.apply(algebre.limits.separate)    


if __name__ == '__main__':
    prove(__file__)

