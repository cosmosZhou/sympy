from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(x):
    return Unequal(alpha(x), 0)


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(x[:n])
    
    Eq << discrete.imply.is_positive.alpha.apply(x, n)
    
    Eq << Eq[-1].apply(algebra.is_positive.imply.is_nonzero)


if __name__ == '__main__':
    prove()

