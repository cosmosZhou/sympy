from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol

@plausible
def apply(n, k):
    return Equality(binomial(n, k), binomial(n, n - k))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    k = Symbol('k', integer=True)

    Eq << apply(n, k)
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
