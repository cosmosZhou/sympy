from util import *


@apply
def apply(self):
    function, (x,) = self.of(Sum)
    x, (start, stop) = x.of(Sliced)
    assert start + 1 < stop
    return Equal(self, Sum[x[start], x[start + 1:stop]](function))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]](f(x[i:n])))


if __name__ == '__main__':
    run()

# created on 2020-03-18
