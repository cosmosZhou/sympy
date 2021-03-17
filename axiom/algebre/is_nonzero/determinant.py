from axiom.utility import prove, apply
from sympy.core.relational import Equality, Unequal

from sympy.matrices.expressions.determinant import Determinant
from sympy.matrices.expressions.cofactor import Cofactors

from sympy import Symbol
from sympy.matrices.expressions.inverse import Inverse
from axiom import algebre, discrete


@apply
def apply(given):   
    assert given.is_Unequality
    A_det, zero = given.args
    assert A_det.is_Determinant
    assert zero.is_zero
    A = A_det.arg
    return Equality(Cofactors(A).T / Determinant(A), Inverse(A))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(complex=True, shape=(n, n))
    Eq << apply(Unequal(Determinant(A), 0))
    
    Eq << discrete.matrix.determinant.adjugate.apply(A)
    
    Eq << algebre.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].inverse()
    
    Eq << algebre.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].lhs.args[0].base @ Eq[-1] 
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
