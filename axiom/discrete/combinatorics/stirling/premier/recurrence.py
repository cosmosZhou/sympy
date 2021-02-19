from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling1
from sympy import Symbol

@apply
def apply(n, k):
    return Equality(Stirling1(n + 1, k + 1), Stirling1(n, k) + (n + 1) * Stirling1(n, k + 1))




@prove
def prove(Eq):
    k = Symbol.k(integer=True, nonnegative=True)

    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n, k)

    
if __name__ == '__main__':
    prove(__file__)

