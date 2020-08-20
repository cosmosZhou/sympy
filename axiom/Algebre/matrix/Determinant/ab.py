from sympy.core.symbol import Symbol
from sympy.utility import plausible, Ref, identity
from sympy.core.relational import Equality
from sympy import S

from sympy.matrices.expressions.determinant import det, Determinant
from sympy.matrices.dense import Matrix
from sympy.functions.elementary.miscellaneous import Min, Max
from sympy.concrete.products import Product
from sympy.matrices.expressions.matexpr import Multiplication


@plausible
def apply(a, b):
    n = a.shape[0]
    
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    
    return Equality(Determinant(Ref[i:n, j:n](a[Min(i,j)] * b[Max(i,j)])), 
                    a[0] * b[n-1] * Product(a[i] * b[i-1] - a[i-1] * b[i], (i, 1, n-1)))


from sympy.utility import check


@check
def prove(Eq):
    n = 4
    a = Symbol('a', shape=(n,), complex=True, zero=False)
    b = Symbol('b', shape=(n,), complex=True, zero=False)
    Eq << apply(a, b)
 
    L = Symbol('L', shape=(n, n), definition=Eq[0].lhs.arg)
    Eq << identity(L).definition
    
    Eq << Eq[-1].this.rhs.as_Matrix()
    return
    Eq << Eq[-1] @ Multiplication(n, 0, 1 / a[0])
    
    Eq << Eq[-1] @ Multiplication(n, 3, 1 / b[3])
    
    Eq << Eq[-1] @ Multiplication(n, 2, 1 / b[2])
    
    Eq << Multiplication(n, 3, b[2]) @ Eq[-1] 
    
    Eq << Eq[-1].det()
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    prove(__file__)
