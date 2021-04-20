from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import HK
from axiom.discrete.imply.is_positive.alpha import alpha


def AHK(x):
    H, K = HK(x)
    n = H.definition.variable
    A = Symbol.alpha(LAMBDA[n](alpha(x[:n + 1])))
    return A, H, K


@apply
def apply(x, n):
    A, H, K = AHK(x)
    return Equal(A[n], H[n] / K[n])


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True)
    
    Eq << apply(x, n)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].base.definition
    
    Eq << discrete.continued_fraction.alpha.HK.provided.is_positive.apply(x[:n + 1])

    
if __name__ == '__main__':
    prove()

