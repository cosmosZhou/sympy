from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Ref, identity

from sympy.utility import Sum

from sympy.functions.combinatorial.numbers import Stirling
from sympy.axiom.discrete.combinatorics import stirling
from sympy.tensor.indexed import IndexedBase
from sympy import axiom
from sympy.axiom.discrete import difference
from sympy.axiom import discrete


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

    cout << stirling.second.recurrence.apply(n, k)

    cout << Eq[-1].subs(Eq[0])

    from sympy import oo
    y = IndexedBase('y', (oo,), definition=Ref[n](Stirling(n, k + 1)))

    cout << Equality.by_definition_of(y)

    cout << Eq[-1].subs(n, n + 1)

    cout << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    cout << Eq[-1].rsolve(y[n])

    cout << Eq[-1].subs(Eq[3])

    cout << Eq[-1].subs(n, k + 1)

    cout << Eq[-1].solve(Eq[-1].exists)
    cout << Eq[-1].right.powsimp(deep=True)

    l = Eq[0].rhs.args[1].limits[0][0]
    cout << identity(binomial(k + 1, l)).rewrite(factorial)

    cout << axiom.discrete.combinatorics.factorial.expand.apply(k - l + 1)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1] / factorial(k + 1)

    cout << Eq[-1].reversed

    cout << axiom.discrete.combinatorics.factorial.expand.apply(k + 1)
    cout << Eq[10].subs(Eq[-2], Eq[-1])

    cout << Eq[-1].right.expand(deep=False)

    cout << Eq[-1].right.args[1].args[-1].simplifier()

    cout << Eq[-1].right.args[1].args[0].expand(power_base=True)

    cout << Eq[-1].right.powsimp()

    x = Symbol('x')

    cout << difference.definition.apply(x ** (k + 1), x, k + 1)

    cout << difference.factorial.apply(x, k + 1)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(x, 0)

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1] * (-1) ** (k + 1)

    cout << Eq[-1].right.as_one_term()

    cout << Eq[-1].right.function.powsimp(combine='exp')

    cout << Eq[-1].right.bisect(back=1)

    cout << Eq[-1] - Eq[-1].rhs.args[0]

    cout << Eq[21].subs(Eq[-1].reversed, Eq[16])

    cout << Eq[-1].right.expand()

    cout << Eq[-1].right.ratsimp()

    cout << Eq[-1].subs(Eq[16].right.expand().reversed)

    cout << Eq[7].subs(Eq[-1])

    cout << discrete.combinatorics.binomial.expand.apply(k + 1, k - l + 1)

    cout << discrete.combinatorics.binomial.complement.apply(k, l)
    cout << discrete.combinatorics.binomial.complement.apply(k + 1, l)

    cout << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    cout << Eq[-1] / (k + 1)

    cout << Eq[36].subs(Eq[-1].reversed)

    cout << Eq[-1].right.args[1].args[-1].simplifier()

    cout << Eq[-1].subs(Eq[16].reversed)

    cout << Eq[-1] * factorial(k + 1)
    cout << Eq[-1].expand()

    cout << Eq[-1].right.args[1].as_one_term()

    cout << Eq[-1].right.args[1].function.powsimp()

    cout << Eq[0].subs(k, k + 1) * factorial(k + 1)

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1].right.bisect(back=1)


if __name__ == '__main__':
    prove()
