from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling1


@plausible
def apply(n, k):
    return Equality(Stirling1(n + 1, k + 1), Stirling1(n, k) + (n + 1) * Stirling1(n, k + 1))


from sympy.utility import check


@check
def prove(Eq):
    k = Symbol('k', integer=True, nonnegative=True)

    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(n, k)

    
if __name__ == '__main__':
    prove(__file__)

