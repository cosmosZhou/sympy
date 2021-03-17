from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply
def apply(n):
    k = Symbol.k(integer=True)
    
    return Equality(LAMBDA[k:n + 1](KroneckerDelta(k, n)),
                    BlockMatrix(ZeroMatrix(n), 1))


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    U = Symbol.U(Eq[0].lhs)
    V = Symbol.V(Eq[0].rhs)
    
    assert V.is_complex
    assert V.is_real
    assert V.is_rational
    assert V.is_integer
    
    Eq << U.this.definition
    Eq << V.this.definition
    
    i = Symbol.i(integer=True, domain=[0, n])
    
    Eq << Eq[-1][i]
    
    Eq << U[i].this.definition
    
    Eq << Eq[-2].this.rhs.astype(KroneckerDelta)
    
    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].apply(algebre.eq.imply.eq.lamda, (i,), simplify=False)
    
    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2]).reversed
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
