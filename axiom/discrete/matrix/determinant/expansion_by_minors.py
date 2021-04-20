from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.cofactor import Cofactors
from axiom import algebra


@apply
def apply(A, i=None, j=None):
#         https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html    
    n = A.shape[0]
    if i is not None:
        i = sympify(i)
        j = A.generate_free_symbol(excludes=i.free_symbols, integer=True)
        sigmar = Sum[j:n]
    else:
        j = sympify(j)
        i = A.generate_free_symbol(excludes=j.free_symbols, integer=True)
        sigmar = Sum[i:n]
        
    return Equal(Det(A), sigmar(A[i, j] * Cofactors(A)[i, j]).simplify())


@prove
def prove(Eq):    
    print('this is a validation, not a proof in', __file__)
    n = Symbol.n(integer=True, positive=True)
    n = 5
    i = Symbol.i(integer=True, positive=True)
    i = 4
    A = Symbol.A(shape=(n, n), complex=True, zero=False)
    Eq << apply(A, i=i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Eq[-1].this.rhs.args[0].args[1].arg.astype(Matrix)
    
    Eq << Eq[-1].this.rhs.args[1].args[2].arg.astype(Matrix)
    
    Eq << Eq[-1].this.rhs.args[2].args[1].arg.astype(Matrix)
    
    Eq << Eq[-1].this.rhs.args[3].args[2].arg.astype(Matrix)
    
    Eq << Eq[-1].this.rhs.args[4].args[1].arg.astype(Matrix)
    
    Eq << Eq[-1].this.lhs.arg.astype(Matrix)
    
    Eq << Eq[-1].doit(deep=True)
    
    Eq << Eq[-1].this.rhs.expand()

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
