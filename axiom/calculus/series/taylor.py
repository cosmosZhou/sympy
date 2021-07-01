from util import *


@apply
def apply(n):
    k = Symbol.k(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)


if __name__ == '__main__':
    run()

