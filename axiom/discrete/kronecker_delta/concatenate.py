from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Concatenate, ZeroMatrix
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(W):
    n = W.shape[0]
    k = Symbol.k(integer=True)
    
    return Equality(Concatenate(Concatenate(W.T, ZeroMatrix(n)).T,
                                LAMBDA[k:n + 1](KroneckerDelta(k, n))),
                    Concatenate(Concatenate(W, ZeroMatrix(n)).T,
                                LAMBDA[k:n + 1](KroneckerDelta(k, n))).T)


@check
def prove(Eq):
    n = Symbol.n(domain=[2, oo], integer=True)
    W = Symbol.W(shape=(n, n), complex=True)
    Eq << apply(W)
    
    U = Symbol.U(definition=Eq[0].lhs)
    V = Symbol.V(definition=Eq[0].rhs)
    
    Eq << U.this.definition
    Eq << V.this.definition
        
    i = Symbol.i(integer=True, domain=[0, n])
    j = Symbol.j(integer=True, domain=[0, n])
    
    Eq << (V[i, j].this.definition, U[i, j].this.definition)
    
    Eq << (Eq[-1].this.rhs.as_KroneckerDelta(), Eq[-2].this.rhs.as_KroneckerDelta())
    
    Eq << Eq[-2] - Eq[-1]
    
    Eq << Eq[-1].reference((j,), (i,))

    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2])
    
    Eq << Eq[-1].forall((j,), (i,))        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
