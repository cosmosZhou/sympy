
from sympy.core.relational import Equality

from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Addition
from sympy import LAMBDA
from sympy import Symbol

@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol.w(definition=LAMBDA[j, i](Addition(n, i, j, lamda)))
        w_quote = Symbol.w_quote(definition=LAMBDA[j, i](Addition(n, i, j, -lamda)))
    else:
        assert w[i, j] == Addition(n, i, j, lamda)
        assert w_quote[i, j] == Addition(n, i, j, -lamda)
    
    return Equality(w_quote[i, j] @ w[i, j] @ x, x)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n,), real=True)
    lamda = Symbol.lamda(real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices    

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base
    
    Eq << (w[i, j] @ x).this.subs(Eq[1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.function.args[1]().expr.simplify()
    
    Eq << (w_quote[i, j] @ Eq[-1]).this.rhs.subs(Eq[0])    

    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.function.simplify(wrt=j)

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
