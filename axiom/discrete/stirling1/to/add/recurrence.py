from util import *


@apply
def apply(n, k):
    from sympy.functions.combinatorial.numbers import Stirling1
    return Equal(Stirling1(n + 1, k + 1), Stirling1(n, k) + (n + 1) * Stirling1(n, k + 1))


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True, nonnegative=True)

    Eq << apply(n, k)


if __name__ == '__main__':
    run()

# created on 2021-07-31
