from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.matrices.expressions.determinant import Determinant
from sympy.concrete.products import Product
from sympy.concrete.expr_with_limits import Ref
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete.summations import Sum 


@plausible
def apply(a):
    n = a.shape[0]
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    return Equality(Determinant(1 + Ref[i:n, j:n](a[i] * KroneckerDelta(i, j))),
                    (1 + Sum[i:0:n - 1](1 / a[i])) * Product[i:0:n - 1](a[i]))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, positive=True)
    a = Symbol('a', shape=(n,), complex=True, zero=False)
    Eq << apply(a)
 

if __name__ == '__main__':
    prove(__file__)
