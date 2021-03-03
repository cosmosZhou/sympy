from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Shift


@apply
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol.w(LAMBDA[j, i](Shift(n, i, j)))
    else:
        assert w[i, j] == Shift(n, i, j)
    
    return Equality(w[i, j].T @ w[i, j] @ x, x)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(x)
    
    Eq << Eq[0].T
    
    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    
    Eq << (w[i, j] @ x).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs().function.args[2]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << (w[i, j].T @ Eq[-1]).this.rhs.subs(Eq[0])
     
    Eq << Eq[-1].this.rhs.expand()

#     Eq << Eq[-1].this.rhs.function.args[1]().expr.args[0].cond.simplify()
    
    Eq << Eq[-1].this.rhs.function.args[1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs().function.args[2]().expr.simplify(wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.rhs().function.args[1]().expr.simplify()
        

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
