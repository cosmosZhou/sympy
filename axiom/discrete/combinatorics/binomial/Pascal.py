from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import plausible, Eq

from sympy import Symbol
@plausible
def apply(n, k):
    return Equality(binomial(n, k), binomial(n - 1, k) + binomial(n - 1, k - 1))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)
    
    k = Symbol.k(integer=True)
    
    Eq << apply(n, k)
#     n, k = Eq[-1].forall
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
