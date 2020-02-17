from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, Union
from sympy.core.symbol import Symbol
from sympy.functions.special.gamma_functions import gamma
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval, FiniteSet
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset


@plausible
def apply(n):
    x = IndexedBase('x', (oo,), integer=True, nonnegative=True)
    
    return Equality(abs(conditionset(x[:n], Equality(x[:n].set, Interval(0, n - 1, integer=True)))), factorial(n))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(n)
#     Eq << Eq[0].rewrite(gamma).expand(func=True)


if __name__ == '__main__':
    prove(__file__)
