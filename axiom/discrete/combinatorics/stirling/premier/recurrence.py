from util import *


@apply
def apply(n, k):
    from sympy.functions.combinatorial.numbers import Stirling1
    return Equal(Stirling1(n + 1, k + 1), Stirling1(n, k) + (n + 1) * Stirling1(n, k + 1))


@prove(surmountable=False)
def prove(Eq):
    k = Symbol.k(integer=True, nonnegative=True)

    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n, k)

    
if __name__ == '__main__':
    run()

