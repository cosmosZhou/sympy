from util import *


@apply(given=None)
def apply(self, y):
    solution = rsolve(self, y, symbols=True)
    if solution is None:
        return
    solution, limits = solution

    eq = self.func(y, solution)
    if len(limits) == 0:
        return eq

    for i, C in enumerate(limits):
        limits[i] = (C,)
    return Equivalent(self, Any(eq, *limits))


@prove(proved=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    k, n = Symbol(integer=True)
    c = Symbol(real=True, positive=True)
    i = Symbol(domain=Range(0, k + 1))

    y = Symbol(real=True, shape=(oo,))

    Eq << apply(Equal(y[n + 1], y[n] * (k + 1) + i ** n), y=y[n])


if __name__ == '__main__':
    run()
