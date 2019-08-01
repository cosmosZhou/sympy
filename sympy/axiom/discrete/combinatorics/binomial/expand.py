from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq
from sympy.core.symbol import Symbol


def apply(n=None, k=None):
    for_clause = None
    if n is None:
        n = Symbol('n', integer=True)
        for_clause = n

    if k is None:
        k = Symbol('k', integer=True)
        if for_clause is None:
            for_clause = k
        else:
            for_clause = [n, k]

    return Equality(binomial(n, k), n / k * binomial(n - 1, k - 1),
                    plausible=plausible(),
                    for_clause=for_clause)


from sympy.utility import check


@check
def prove():
    cout << apply()
    cout << Eq[-1].combsimp()


if __name__ == '__main__':
    prove()
