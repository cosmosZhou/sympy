from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, factorial(n) / (factorial(k) * factorial(n - k)))


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    Eq << apply(binomial(n, k))


if __name__ == '__main__':
    run()


from . import fallingFactorial
