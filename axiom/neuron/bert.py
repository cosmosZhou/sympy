from sympy.core.symbol import Symbol
from sympy.utility import plausible, identity
from sympy.core.relational import Equality
import sympy
from sympy.functions.elementary.exponential import softmax


@plausible
def apply(n, d):
    Q = Symbol('Q', shape=(n, d), real=True)
    K = Symbol('K', shape=(n, d), real=True)
    V = Symbol('V', shape=(n, d), real=True)
    
    S = Symbol('S', shape=(n, d), definition=softmax(Q @ K.T / sympy.sqrt(d)) @ V)

    return Equality(S[0], softmax(Q[0] @ K.T / sympy.sqrt(d)) @ V)


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)

    Eq << apply(n, d)
    
    M = Symbol('M', shape=(n, n), definition=Eq[0].rhs.args[0].arg)
    Eq << identity(M).definition
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
    Eq << Eq[-1][0]
    
    Eq << Eq[2][0]
    
    Eq << Eq[-2].subs(Eq[-1])
    


if __name__ == '__main__':
    prove(__file__)
