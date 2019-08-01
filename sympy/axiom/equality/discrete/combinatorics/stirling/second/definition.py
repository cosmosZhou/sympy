from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Ref, identity

from sympy.utility import Sum

from sympy.functions.combinatorial.numbers import Stirling
from sympy.axiom.equality.discrete.combinatorics import stirling
from sympy.tensor.indexed import IndexedBase
from sympy import axiom


def apply(n, k):
    free_symbols = n.free_symbols | k.free_symbols
    i = generate_free_symbol(free_symbols, integer=True)
    return Equality(Stirling(n, k), Sum[i:0:k]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    k = Symbol('k', integer=True, nonnegative=True)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n, k)

    cout << Eq[-1].subs(k, 0).doit()

    cout << stirling.second.recurrence.apply(n + 1, k + 1)

    cout << Eq[-1].subs(Eq[0])

    from sympy import oo
    y = IndexedBase('y', (oo,), definition=Ref[n](Stirling(n, k + 1)))

    cout << Equality.by_definition_of(y)

    cout << Eq[-1].subs(n, n + 1)

    cout << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    cout << Eq[-1].rsolve(y[n])

    cout << Eq[-1].subs(Eq[3])

    cout << Eq[-1].subs(n, k + 1)

    cout << Eq[-1].solve(Eq[-1].with_clause)
    cout << Eq[-1].right.powsimp(deep=True)

    l = Eq[0].rhs.args[1].limits[0][0]
    cout << identity(binomial(k + 1, l)).rewrite(factorial)

    cout << axiom.equality.combinatorics.factorial.expand.apply(k - l + 1)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1] / factorial(k + 1)

    cout << Eq[-1].reversed

    cout << axiom.equality.combinatorics.factorial.expand.apply(k + 1)
    cout << Eq[10].subs(Eq[-2], Eq[-1])

    cout << Eq[-1].right.expand(deep=False)

    cout << Eq[-1].right.args[1].args[-1].simplifier()

    cout << Eq[-1].right.args[1].args[0].expand(power_base=True)

    cout << Eq[-1].right.powsimp()


if __name__ == '__main__':
    prove()
