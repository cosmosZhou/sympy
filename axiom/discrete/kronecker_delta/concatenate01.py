from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Concatenate, ZeroMatrix
from sympy import LAMBDA
from sympy import Symbol
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(n):
    k = Symbol.k(integer=True)
    
    return Equality(LAMBDA[k:n + 1](KroneckerDelta(k, n)),
                    Concatenate(ZeroMatrix(n), 1))


@check
def prove(Eq):
    n = Symbol.n(domain=[2, oo], integer=True)
    Eq << apply(n)
    
    U = Symbol.U(definition=Eq[0].lhs)
    V = Symbol.V(definition=Eq[0].rhs)
    
    assert V.is_complex
    assert V.is_real
    assert V.is_rational
    assert V.is_integer
    
    Eq << U.this.definition
    Eq << V.this.definition
    
    i = Symbol.i(integer=True, domain=[0, n])
    
    Eq << Eq[-1][i]
    
    Eq << U[i].this.definition
    
    Eq << Eq[-2].this.rhs.as_KroneckerDelta()
    
    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].reference((i,))
    
    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2]).reversed
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
