from util import *


@apply
def apply(self):
    function, (x,) = self.of(Sum)
    x, (start, stop) = x.of(Slice)
    assert start <= stop - 1
    #allow empty slices in summation??
    return Equal(self, Sum[x[start:stop - 1], x[stop - 1]](function))


@prove(provable=False)
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    i = Symbol.i(domain=Range(0, n))
    x = Symbol.x(integer=True, shape=(oo,))
    f = Function.f(real=True, shape=())
    Eq << apply(Sum[x[i:n + 1]](f(x[i:n + 1])))


if __name__ == '__main__':
    run()