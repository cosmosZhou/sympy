from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq
from sympy.core.symbol import Symbol


def apply(n, k):
    return Equality(binomial(n, k), binomial(n, n - k), plausible=plausible())


from sympy.utility import check


@check
def prove():
    n = Symbol('n', integer=True)
    k = Symbol('k', integer=True)

    cout << apply(n, k)
    cout << Eq[-1].combsimp()


if __name__ == '__main__':
    prove()
