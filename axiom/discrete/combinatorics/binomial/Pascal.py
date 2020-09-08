from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, Eq
from sympy.core.symbol import Symbol
from sympy import var
@plausible
def apply(n, k):
    return Equality(binomial(n, k), binomial(n - 1, k) + binomial(n - 1, k - 1))


from sympy.utility import check


@check
def prove(Eq):
    n = var(integer=True).n
    
    k = var(integer=True).k
    
    Eq << apply(n, k)
#     n, k = Eq[-1].forall
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
