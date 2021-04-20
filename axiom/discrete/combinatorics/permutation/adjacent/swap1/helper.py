from sympy import *
from axiom.utility import prove, apply

from sympy.matrices.expressions.matexpr import Swap
from axiom import algebra, discrete


@apply
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    if w is None:
        w = Symbol.w(LAMBDA[j](Swap(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == Swap(n, 0, j)
    
    return Equal(LAMBDA[i:n](x[w[j][i] @ LAMBDA[i:n](i)]), LAMBDA[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(etype=dtype.integer, shape=(n,))    
    
    Eq << apply(x)    
    
    w = Eq[0].lhs.base
    
    Eq << discrete.combinatorics.permutation.adjacent.swap1.eq.apply(x, w)
    
    i, j = Eq[-1].rhs.args[0][1].args
    Eq << Eq[-1].apply(algebra.cond.imply.forall.restrict, (i,), (j,))
    
    _i = i.unbounded
    Eq << Eq[-1].this.lhs.args[1].args[1].limits_subs(i, _i)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (_i, 0, n), simplify=False)   
    

if __name__ == '__main__':
    prove()
