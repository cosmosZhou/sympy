from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval


@plausible
def apply(n):
    x = Symbol('x', shape=(oo,), integer=True, nonnegative=True)
    
    return Equality(abs(conditionset(x[:n], Equality(x[:n].set, Interval(0, n - 1, integer=True)))), factorial(n))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(n)
#     Eq << Eq[0].rewrite(gamma).expand(func=True)


if __name__ == '__main__':
    prove(__file__)
