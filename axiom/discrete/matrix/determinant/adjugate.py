from axiom.utility import prove, apply
from sympy import *
from sympy.matrices.expressions.cofactor import Cofactors


@apply
def apply(A): 
    n = A.shape[0]        
    return Equal(A @ Cofactors(A).T, Determinant(A) * Identity(n))


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(complex=True, shape=(n, n))
    Eq << apply(A)

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
