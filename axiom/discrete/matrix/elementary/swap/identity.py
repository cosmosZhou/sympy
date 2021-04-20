from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import algebra


@apply
def apply(x, w=None, left=True, reference=True):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)
    
    if w is None:
        w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
    
    if left:
        if reference:
            return Equal(LAMBDA[k:n](x[w[i, j, k] @ LAMBDA[k:n](k)]), w[i, j] @ x)
        else:
            return Equal(x[w[i, j, k] @ LAMBDA[k:n](k)], w[i, j, k] @ x)
    else:
        if reference:
            return Equal(LAMBDA[k:n](x[LAMBDA[k:n](k) @ w[i, j, k]]), x @ w[i, j])
        else:
            return Equal(x[LAMBDA[k:n](k) @ w[i, j, k]], x @ w[i, j, k])


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(x)
    
    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    
    k = Eq[1].lhs.variable
    
    Eq << (Eq[0].lhs[k] @ LAMBDA[k:n](k)).this.args[0].definition  
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this(i).rhs.args[0].expr.simplify()
    Eq << Eq[-1].this(j).rhs.args[1].expr.simplify()
    Eq << Eq[-1].this(k).rhs.args[2].simplify()
    
    Eq.lhs_assertion = x[Eq[-1].lhs].this.subs(Eq[-1]).this.rhs.expand()
    
    Eq << (w[i, j] @ x).this.subs(Eq[0])
    
    Eq << Eq[-1].subs(Eq[-1].rhs.this.expand())
    
    Eq << Eq[-1][k]
    
    Eq << Eq.lhs_assertion.subs(Eq[-1].reversed)
    
    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (k, 0, n))


if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
