from util import *


@apply
def apply(x, i=None, j=None, w=None):
    n = x.shape[0]
    if i is None:
        i = Symbol.i(domain=Range(0, n))
        
    if j is None:
        j = Symbol.j(domain=Range(0, n))
    
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    
    return Equal(w[i, j] @ w[i, j] @ x, x)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    
    Eq << (w[i, j] @ x).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << (w[i, j] @ Eq[-1]).this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Piecewise)
        

if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
