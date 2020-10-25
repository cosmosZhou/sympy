from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.functions.special.gamma_functions import gamma
from sympy import Symbol

@plausible
def apply(n):
    return Equality(factorial(n), n * factorial(n - 1))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)
    Eq << Eq[0].rewrite(gamma).expand(func=True)


if __name__ == '__main__':
    prove(__file__)
