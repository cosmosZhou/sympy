from util import *


@apply
def apply(self):
    function, (x,) = self.of(Minima)
    x, (start, stop) = x.of(Sliced)
    assert start <= stop - 1
    #allow empty slices in summation??
    return Equal(self, Minima[x[start:stop - 1], x[stop - 1]](function))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Minima[x[i:n + 1]](f(x[i:n + 1])))


if __name__ == '__main__':
    run()
# created on 2020-12-18
