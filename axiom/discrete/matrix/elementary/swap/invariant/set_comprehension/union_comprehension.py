from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import algebra, sets


@apply
def apply(x, w=None, right=None, free_symbol=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    if w is None: 
        w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap        
    
    if right:
        lhs = (x @ w[i, j]).set_comprehension(free_symbol=free_symbol)
    else:
        lhs = (w[i, j] @ x).set_comprehension(free_symbol=free_symbol)
    return Equal(lhs, x.set_comprehension(free_symbol=free_symbol))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), integer=True)    
    
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices
    
    k = Eq[1].lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0].lhs[k].this.definition
    
    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].apply(sets.eq.imply.eq.set_comprehension, (k, 0, n))
    
    Eq << Eq[-1].this.find(Complement[Complement]).apply(sets.complement.to.union.intersection)
    
    Eq << Eq[-1].this(i, j).find(Unequal, Intersection).simplify()
    
    Eq << Eq[-1].this(i, j).find(NotSubset, Intersection).simplify()
    
    Eq << Eq[-1].this(i, j).find(Contains[Intersection]).simplify()
    
    Eq << Eq[-1].this(i, j).find(Intersection).simplify()
    
    Eq << Eq[-1].this.rhs.args[1]().expr.find(Intersection).simplify()
    
    Eq << Eq[-1].this.lhs.apply(sets.union_comprehension.limits.domain_defined.insert)
    
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, i)
    
    Eq << Eq[-1].this.rhs.apply(sets.union_comprehension.limits.domain_defined.insert)
    
        
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

