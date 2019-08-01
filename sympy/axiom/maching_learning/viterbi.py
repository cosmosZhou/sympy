from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, Min
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase


def apply(G, x, y):
    n, d = x.shape
    i = Symbol('i', integer=True)
    t = Symbol('t', integer=True)

    s = IndexedBase('s', (n,),
                    definition=Ref[t](Sum[i:1: t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    x_quote = IndexedBase("x'", (n, d),
                          definition=Ref[t](Ref[y[t]](Min[y[0:t]](s[t]))))

    return Equality(x_quote[t + 1], x[t + 1] + Min(x_quote[t] + G),
                    for_clause=t,
                    definition=[s, x_quote])


from sympy.utility import check
@check
def prove():
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)

    # n is the length of the sequence
    # d is the number of output labels
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (n, d))
    y = IndexedBase('y', (n,))

    cout << apply(G, x, y)
    s, x_quote = Eq[0].definition

    cout << Equality.by_definition_of(x_quote)
    cout << Equality.by_definition_of(s)

    t = Eq[0].for_clause

    Eq2 = Eq[-1].subs(t, t + 1)
    Eq2 -= Eq[-1]
    cout << Eq2.right.simplifier() + s[t]

    cout << Eq[1].subs(t, t + 1)

    cout << Eq[-1].right.subs(Eq[-2])

    cout << Eq[-1].right.function.simplifier()

    cout << Eq[-1].right.args[1].function.as_separate_limits()

    cout << Eq[-1].right.args[1].function.as_Ref()

    cout << Eq[-1].right.args[1].as_Min()

    cout << Eq[-1].right.subs(Eq[1].reversed)

    cout << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove()
