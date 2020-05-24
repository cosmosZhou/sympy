from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, plausible
from sympy.core.relational import Unequality

@plausible
def apply(x, y, z, n):
    return Unequality(x ** n + y ** n, z ** n)


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, domain=Interval(3, oo, integer=True))
    x = Symbol('x', integer=True, nonnegative=True)
    y = Symbol('y', integer=True, nonnegative=True)
    z = Symbol('z', integer=True, nonnegative=True)
    
    Eq << apply(x, y, z, n)


if __name__ == '__main__':
    prove(__file__)
