from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.functions.elementary.piecewise import Piecewise
from sympy import UNION, LAMBDA
from sympy.core.numbers import oo
from sympy.sets.sets import Interval


@plausible
def apply(n, k, s1=None, A=None):    
    j = Symbol.j(domain=Interval(0, k, integer=True))
            
    if s1 is None:
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s1 = Symbol.s1(definition=UNION[x[:k + 1]:Stirling.conditionset(n, k + 1, x)]({x[:k + 1].set_comprehension()}))
            
    if A is None:
        x = s1.definition.variable.base
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", definition=Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", definition=LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equality(i, j)), (x[i], True))))
        A = Symbol.A(definition=LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        
    return Equality(abs(s1), abs(A[j]))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    i, j = Eq[1].rhs.args[0].cond.args
    x = Eq[1].rhs.args[1].expr.base
    x_hat = Symbol(r"\hat{x}", definition=LAMBDA[i:k + 1](Piecewise((x[i] - {n} , Equality(i, j)), (x[i], True))))

    Eq.x_hat_definition = x_hat.this.definition[i]
    
    s1 = Eq[0].lhs
    x_quote = Eq[1].lhs.base
    Aj = Eq[3].lhs    
    e = Symbol.e(**s1.etype.dict)
    
if __name__ == '__main__':
    prove(__file__)

