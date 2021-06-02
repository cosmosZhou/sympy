from util import *


@apply
def apply(x, y, z, n):
    return Unequal(x ** n + y ** n, z ** n)


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(domain=Range(3, oo))
    x = Symbol.x(integer=True, nonnegative=True)
    y = Symbol.y(integer=True, nonnegative=True)
    z = Symbol.z(integer=True, nonnegative=True)
    
    Eq << apply(x, y, z, n)


if __name__ == '__main__':
    run()
