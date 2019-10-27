from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, Min, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase


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


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)

    # n is the length of the sequence
    # d is the number of output labels
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (n, d))
    y = IndexedBase('y', (n,))

    Eq.recursion, Eq.aggregate = apply(G, x, y)
    x_quote = Eq.recursion.lhs.base

    Eq.x_quote_definition = Equality.by_definition_of(x_quote)

    s = Eq.x_quote_definition.rhs.function.function.base
    Eq << Equality.by_definition_of(s)

    t = Eq.recursion.lhs.indices[0] - 1
    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1] - Eq[-2]

    Eq << Eq[-1].this.rhs.simplifier() + s[t]

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplifier()

    Eq << Eq[-1].this.rhs.args[1].function.bisect(back=1)

    Eq << Eq[-1].this.rhs.args[1].function.as_Ref()

    Eq << Eq[-1].this.rhs.args[1].as_Min()

    Eq << Eq[-1].this.rhs.subs(Eq.x_quote_definition.reversed)

    Eq << Eq.aggregate.this.lhs.bisect(back=1)

    Eq << Eq[-1].this.lhs.as_Ref()

    Eq << Eq.x_quote_definition.subs(t, n - 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    prove(__file__)
