from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, Min, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
import sympy


def apply(G, x, y):
    n, d = x.shape
    i = Symbol('i', integer=True)
    t = Symbol('t', integer=True)

    s = IndexedBase('s', (n,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    x_quote = IndexedBase("x'", (n, d),
                          definition=Ref[t](Ref[y[t]](Min[y[0:t]](s[t]))))

    return Equality(x_quote[t + 1], x[t + 1] + Min(x_quote[t] + G), plausible=plausible()), \
        Equality(Min[y](s[n - 1]), Min(x_quote[n - 1]), plausible=plausible())


def softmax(v):
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)    
    return Ref[i:0:v.shape[1], j:0:v.shape[1]] (sympy.exp(v[i, j]) / Sum[j:0:v.shape[1]](sympy.exp(v[i, j])))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)

    # n is the length of the sequence
    # d is the embedding size
    Q = IndexedBase('Q', (n, d))
    K = IndexedBase('K', (n, d))
    V = IndexedBase('V', (n, d))
    
    S = IndexedBase('S', (n, d))

    Eq << Equality(S, softmax(Q @ K.transpose() / sympy.sqrt(d)) @ V)


if __name__ == '__main__':
    prove(__file__)
