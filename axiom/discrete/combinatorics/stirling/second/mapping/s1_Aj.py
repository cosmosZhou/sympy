from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from sympy import *


@apply
def apply(n, k, s1=None, A=None): 
    j = Symbol.j(domain=Interval(0, k, integer=True))
            
    if s1 is None:
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s1 = Symbol.s1(UNION[x[:k + 1]:Stirling.conditionset(n, k + 1, x)]({x[:k + 1].set_comprehension()}))
            
    if A is None:
        x = s1.definition.variable.base
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol.A(LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        
    return Equal(abs(s1), abs(A[j]))


@prove(surmountable=False)
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    i, j = Eq[1].rhs.args[0].cond.args
    x = Eq[1].rhs.args[1].expr.base
    x_hat = Symbol(r"\hat{x}", LAMBDA[i:k + 1](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))

    Eq.x_hat_definition = x_hat.this.definition[i]
    
    s1 = Eq[0].lhs
    x_quote = Eq[1].lhs.base
    Aj = Eq[3].lhs    
    e = Symbol.e(**s1.etype.dict)

    
if __name__ == '__main__':
    prove()

