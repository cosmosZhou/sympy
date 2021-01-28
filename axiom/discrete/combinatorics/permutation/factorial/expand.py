from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from axiom.utility import prove, apply

from sympy.functions.special.gamma_functions import gamma
from sympy import Symbol

@apply(imply=True)
def apply(n):
    return Equality(factorial(n), n * factorial(n - 1))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)
    Eq << Eq[0].rewrite(gamma).expand(func=True)


if __name__ == '__main__':
    prove(__file__)
