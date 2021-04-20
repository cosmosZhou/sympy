from axiom.utility import prove, apply
from sympy import *


@apply
def apply(x, y, z, n):
    return Unequal(x ** n + y ** n, z ** n)


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(domain=Interval(3, oo, integer=True))
    x = Symbol.x(integer=True, nonnegative=True)
    y = Symbol.y(integer=True, nonnegative=True)
    z = Symbol.z(integer=True, nonnegative=True)
    
    Eq << apply(x, y, z, n)


if __name__ == '__main__':
    prove()
