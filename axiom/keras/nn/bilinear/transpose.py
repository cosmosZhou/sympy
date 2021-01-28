from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy.concrete.summations import Sum
from axiom import algebre

@apply(imply=True)
def apply(x, y, W):    
    return Equality(x @ W @ y, y @ W.T @ x)




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n,), real=True)
    W = Symbol.W(shape=(n, n), real=True)
     
    Eq << apply(x, y, W)
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    Eq << (x @ W).this.expand(free_symbol={i, j})
    
    Eq << Eq[-1] @ y
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq.expansion = Eq[-1].this.rhs.function.astype(Sum)
    
    Eq << Eq.expansion.subs(W, W.T)
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.swap, x, y)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, j)
    
    Eq << Eq[-1].this.rhs.limits_swap()
    
    Eq << Eq.expansion.subs(Eq[-1].reversed)


if __name__ == '__main__':
    prove(__file__)
