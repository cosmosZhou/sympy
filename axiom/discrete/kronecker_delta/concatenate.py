from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply
def apply(W):
    n = W.shape[0]
    k = Symbol.k(integer=True)
    
    return Equality(BlockMatrix(BlockMatrix(W.T, ZeroMatrix(n)).T,
                                LAMBDA[k:n + 1](KroneckerDelta(k, n))),
                    BlockMatrix(BlockMatrix(W, ZeroMatrix(n)).T,
                                LAMBDA[k:n + 1](KroneckerDelta(k, n))).T)


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    W = Symbol.W(shape=(n, n), complex=True)
    Eq << apply(W)
    
    U = Symbol.U(definition=Eq[0].lhs)
    V = Symbol.V(definition=Eq[0].rhs)
    
    Eq << U.this.definition
    Eq << V.this.definition
        
    i = Symbol.i(integer=True, domain=[0, n])
    j = Symbol.j(integer=True, domain=[0, n])
    
    Eq <<= V[i, j].this.definition, U[i, j].this.definition
    
    Eq <<= Eq[-1].this.rhs.astype(KroneckerDelta), Eq[-2].this.rhs.astype(KroneckerDelta)
    
    Eq << Eq[-2] - Eq[-1]
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.lamda, (j,), (i,))

    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2]).reversed
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
