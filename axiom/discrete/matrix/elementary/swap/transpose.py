from sympy import *
from axiom.utility import prove, apply

from sympy.matrices.expressions.matexpr import Swap
from axiom import algebra, discrete


@apply
def apply(w):
    n = w.shape[0]
    i = w.generate_free_symbol(integer=True)
    j = w.generate_free_symbol({i}, integer=True)
    
    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap 
    
    return Equal(w[i, j], w[j, i])


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    assert Identity(n).is_integer
    w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    
    Eq << apply(w)

    Eq << w[j, i].equality_defined()
    
    Eq << Eq[0] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.function.astype(KroneckerDelta)
    
    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.identity)
    
    Eq << discrete.matrix.elementary.swap.square.apply(w)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << w[i, j].inverse() @ Eq[-1]
    
    Eq << Eq[-1].apply(algebra.cond.imply.forall.restrict, (i,), (j,))


if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
