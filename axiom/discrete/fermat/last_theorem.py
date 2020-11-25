
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom.utility import plausible
from sympy.core.relational import Unequality
from sympy.core.symbol import Symbol


@plausible
def apply(x, y, z, n):
    return Unequality(x ** n + y ** n, z ** n)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(domain=Interval(3, oo, integer=True))
    x = Symbol.x(integer=True, nonnegative=True)
    y = Symbol.y(integer=True, nonnegative=True)
    z = Symbol.z(integer=True, nonnegative=True)
    
    Eq << apply(x, y, z, n)


if __name__ == '__main__':
    prove(__file__)
