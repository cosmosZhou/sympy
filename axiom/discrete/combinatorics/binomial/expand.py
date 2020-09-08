from sympy.functions.combinatorial.factorials import Binomial
from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol
from sympy import var

@plausible
def apply(n, k):
    return Equality(Binomial(n, k), n / k * Binomial(n - 1, k - 1))


from sympy.utility import check


@check
def prove(Eq):
    n = var(integer=True).n
    
    k = var(integer=True).k
    
    Eq << apply(n, k)
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
