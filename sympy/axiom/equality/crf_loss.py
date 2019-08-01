from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, Min, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
import sympy
from sympy import log, exp
from sympy.logic.boolalg import plausibles_dict


def apply(G, x, y):
    n, d = x.shape

    i = Symbol('i', integer=True)

    t = Symbol('t', integer=True)

    s = IndexedBase('s', (n,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    z = IndexedBase('z', shape=(n, d),
                    definition=Ref[t](Ref[y[t]](Sum[y[0:t]](sympy.E ** -s[t]))))

    x_quote = IndexedBase("x'", shape=(n, d),
                    definition=-Ref[t](sympy.log(z[t])))

    return Equality(x_quote[t + 1],
                    -log(Sum(exp(-x_quote[t] - G))) + x[t + 1],
                    for_clause=t,
                    definition=[s, z, x_quote],
                    plausible=plausible())


from sympy.utility import check
@check
def prove():
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (n, d))
    y = IndexedBase('y', (n,))

    # n is the length of the sequence
    # d is the number of output labels

    cout << apply(G, x, y)

    s, z, x_quote = Eq[-1].definition

    t = Eq[-1].for_clause

    cout << s[t].has(y[t])
    cout << Equality.by_definition_of(s)
    cout << Equality.by_definition_of(z)

    eq = Eq[-2].subs(t, t + 1) - Eq[-2]
    cout << eq.right.simplifier() + s[t]

    cout << Eq[2].subs(t, t + 1)
    cout << Eq[-1].right.subs(Eq[-2])

    cout << Eq[-1].right.function.simplifier()

    cout << Eq[-1].right.as_two_terms()

    cout << Eq[-1].right.args[0].function.separate()

    cout << Eq[-1].right.args[0].function.as_Ref()

    cout << Eq[-1].right.args[0].function.function.as_two_terms()

    cout << Eq[-1].right.subs(Eq[2].reversed)

    cout << Equality.by_definition_of(x_quote)

    cout << Eq[-1].subs(t, t + 1)

    cout << Eq[-1].right.subs(Eq[-3])

    cout << Eq[-1].right.args[1].as_Add()

    cout << sympy.E ** -Eq[-4].reversed

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].right.args[0].args[1].arg.simplifier()


if __name__ == '__main__':
    prove()
    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))
