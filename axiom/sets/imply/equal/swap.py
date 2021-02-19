from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap


def swap(p, *indices):
    n = p.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    
    (i,), (j,) = indices
    k = Symbol.k(integer=True)
    
    d = LAMBDA[k:n](k) @ w[i, j]
    return LAMBDA[k:n](p[d[k]]) 


swap = Function.swap(eval=swap)

from axiom import discrete


@apply
def apply(x, i=None, j=None):
    assert len(x.shape) == 1
    
    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)
        
    if j is None:
        j = Symbol.j(integer=True)
    
    return Equality(swap[i, j](swap[i, j](x)), x)


@prove
def prove(Eq): 
    n = Symbol.n(positive=True, integer=True)
    
    x = Symbol.x(shape=(n,), etype=dtype.integer)
    
    Eq << apply(x)

    (i,), (j,) = Eq[0].lhs.limits
    
    Eq << Eq[-1].this.lhs.arg.definition
    
    Eq << Eq[-1].this.lhs.definition
    
    w = Eq[-1].lhs.function.indices[0].args[1].base
    
    Eq << discrete.matrix.elementary.swap.identity.apply(w[i, j], left=False, w=w, reference=False)
    
    k = Eq[-1].rhs.args[1].indices[-1]
    
    Eq << Eq[-2].lhs.function.index.this.subs(Eq[-1])
     
    Eq << discrete.matrix.elementary.swap.square.apply(w)
    
    Eq << Eq[-1][k].T
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this(k).rhs.simplify()
    
    Eq << Eq[2].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
