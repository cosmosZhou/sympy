from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
import sympy
from sympy.functions.elementary.exponential import softmax


@plausible
def apply(n, d):
    Q = IndexedBase('Q', (n, d))
    K = IndexedBase('K', (n, d))
    V = IndexedBase('V', (n, d))
    
    S = IndexedBase('S', (n, d), definition=softmax(Q @ K.T / sympy.sqrt(d)) @ V)

    return Equality(S[0], softmax(Q[0] @ K.T / sympy.sqrt(d)) @ V)


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)

    Eq << apply(n, d)
    
    Eq << Eq[0][0]


if __name__ == '__main__':
    prove(__file__)
