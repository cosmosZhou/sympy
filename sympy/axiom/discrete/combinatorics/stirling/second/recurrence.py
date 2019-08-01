from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq

from sympy.functions.combinatorial.numbers import Stirling


def apply(n, k):
    return Equality(Stirling(n, k), Stirling(n - 1, k - 1) + k * Stirling(n - 1, k),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    k = Symbol('k', integer=True, nonnegative=True)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n, k)


if __name__ == '__main__':
    prove()
