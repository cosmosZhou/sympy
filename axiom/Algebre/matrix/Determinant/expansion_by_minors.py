from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.matrices.expressions.determinant import Det
from sympy.matrices.expressions.cofactor import Cofactors
from sympy.concrete.summations import Sum


@plausible
def apply(A, i=None, j=None):
#         https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
    n = A.shape[0]
    if i is not None:
        j = A.generate_free_symbol(excludes={i}, integer=True)
        sigmar = Sum[j:n]
    else:
        i = A.generate_free_symbol(excludes={j}, integer=True)
        sigmar = Sum[i:n]
        
    return Equality(Det(A), sigmar(A[i, j] * Cofactors(A)[i, j]))


from sympy.utility import check


@check
def prove(Eq):    
    n = Symbol('n', integer=True, positive=True)
    i = Symbol('i', integer=True, positive=True)
    A = Symbol('A', shape=(n, n), complex=True, zero=False)
    Eq << apply(A, i=i)

    
if __name__ == '__main__':
    prove(__file__)

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
