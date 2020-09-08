from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Unequality


@plausible
def apply(x, y, z, n):
    return Unequality(x ** n + y ** n, z ** n)


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(3, oo, integer=True))
    x = var(integer=True, nonnegative=True).x
    y = var(integer=True, nonnegative=True).y
    z = var(integer=True, nonnegative=True).z
    
    Eq << apply(x, y, z, n)


if __name__ == '__main__':
    prove(__file__)
