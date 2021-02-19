from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import prove, apply, Eq

from sympy import Symbol
@apply
def apply(n, k):
    return Equality(binomial(n, k), binomial(n - 1, k) + binomial(n - 1, k - 1))




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    
    k = Symbol.k(integer=True)
    
    Eq << apply(n, k)
#     n, k = Eq[-1].forall
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
