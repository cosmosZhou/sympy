from axiom.utility import prove, apply
from sympy.core.relational import Equality

from sympy.matrices.expressions.determinant import Determinant
from sympy.matrices.expressions.cofactor import Cofactors

from sympy import Symbol
from sympy.matrices.expressions.matexpr import Identity


@apply
def apply(A):    
    n = A.shape[0]        
    return Equality(A @ Cofactors(A).T, Determinant(A) * Identity(n))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(complex=True, shape=(n, n))
    Eq << apply(A)
    
if __name__ == '__main__':
    prove(__file__)

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
