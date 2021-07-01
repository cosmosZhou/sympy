from util import *


@apply
def apply(self):
    function, (x,) = self.of(Sum)
    x, *indices = x.of(Slice)
    
    assert len(indices) == 1
    
    start, stop = indices[0]
    assert start + 1 < stop
    return Equal(self, Sum[x[start], x[start + 1:stop]](function))


@prove(provable=False)
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n - 1))
    x = Symbol.x(integer=True, shape=(oo,))
    f = Function.f(real=True, shape=())
    Eq << apply(Sum[x[i:n]](f(x[i:n])))


if __name__ == '__main__':
    run()

from . import cartesianSpace
