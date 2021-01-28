from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
from sympy.matrices.expressions.matexpr import Swap


@apply(imply=True)
def apply(n):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    return Equality(BlockMatrix([[Swap(n, i, j), ZeroMatrix(n)], [ZeroMatrix(n), S.One]]), Swap(n + 1, i, j))


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    Eq << apply(n)

    _, i, j = Eq[0].rhs.args
    _i = i.copy(domain=Interval(0, n - 1, integer=True))
    _j = j.copy(domain=Interval(0, n - 1, integer=True))
    
    W = Symbol.W(definition=Eq[0].lhs._subs(i, _i)._subs(j, _j))
    V = Symbol.V(definition=Eq[0].rhs._subs(i, _i)._subs(j, _j))
    
    Eq << W.this.definition
    Eq << V.this.definition
    
    h = Symbol.h(integer=True, domain=[0, n])
    k = Symbol.k(integer=True, domain=[0, n])

    Eq << (V[h, k].this.definition, W[h, k].this.definition)

    Eq << (Eq[-1].this.rhs.astype(KroneckerDelta), Eq[-2].this.rhs.astype(KroneckerDelta))
    
    Eq << Eq[-2] - Eq[-1] 
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.lamda, (k,), (h,), simplify=False)
    
    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2])
    
    Eq << Eq[-1].apply(algebre.condition.imply.forall.minify, (_i,), (_j,))
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
