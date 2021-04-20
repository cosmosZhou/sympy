from sympy import Symbol
from sympy.core.relational import Equal

from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Multiplication
from sympy import LAMBDA


@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol.w(LAMBDA[i](Multiplication(n, i, lamda)))
        w_quote = Symbol.w_quote(LAMBDA[i](Multiplication(n, i, 1 / lamda)))
    else:
        assert w[i] == Multiplication(n, i, lamda)
        assert w_quote[i] == Multiplication(n, i, 1 / lamda)
    
    return Equal(w_quote[i] @ w[i] @ x, x)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n,), real=True)
    lamda = Symbol.lamda(real=True)
    Eq << apply(x, lamda)

    i, *_ = Eq[0].lhs.indices    

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base
    
    Eq << (w[i] @ x).this.subs(Eq[1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << (w_quote[i] @ Eq[-1]).this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].function.expand()
    
    
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
