from sympy.functions.combinatorial.factorials import Binomial
from sympy.core.relational import Equality
from axiom.utility import prove, apply

from sympy import Symbol


@apply(imply=True)
def apply(n, k):
    return Equality(Binomial(n, k) / n, Binomial(n - 1, k) / (n - k))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    
    k = Symbol.k(integer=True)
    
    Eq << apply(n, k)
    Eq << Eq[-1].combsimp()


if __name__ == '__main__':
    prove(__file__)
