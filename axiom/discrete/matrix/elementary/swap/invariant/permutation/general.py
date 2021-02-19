from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom import discrete, algebre


@apply
def apply(m, d, w=None):
    n = d.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    assert m >= 0
    if w is None:
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
        
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(x, Equality(x.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[x:P](Contains(x @ MatProduct[i:m](w[i, d[i]]), P))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    m = Symbol.m(integer=True, nonnegative=True)
    d = Symbol.d(shape=(n,), integer=True, nonnegative=True)
    
    Eq << apply(m, d)
    
    Eq.induction = Eq[-1].subs(m, m + 1)
    
    w, i, j = Eq[0].lhs.args
    
    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n, w, left=False).subs(i, m).subs(j, d[m])
    
    Eq << Eq[-1].subs(Eq[-1].variable, Eq[2].function.lhs)
    
    Eq << Eq[-1].this.args[0].lhs.simplify()
    
    Eq << Eq[-1].apply(algebre.condition.imply.forall.minify, Eq[-3].limits[0])
    
    Eq <<= Eq[-1] & Eq[2]
    
    Eq << Eq[-1].split()  
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.sufficient.imply.condition.induction.apply(Eq[-1], n=m)    

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
