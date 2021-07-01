from util import *


@apply
def apply(given, a, i=None):
    x, y = given.of(Equal)
    assert x.shape == y.shape    
    if i is None:
        return Equal(a[x], a[y])
    n = x.shape[0]
    return Equal(Lamda[i:n](a[x[i]]), Lamda[i:n](a[y[i]]))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(n,), integer=True)
    y = Symbol.y(shape=(n,), integer=True)
    a = Symbol.a(shape=(n,), etype=dtype.integer)
    i = Symbol.i(integer=True)
    
    Eq << apply(Equal(x, y), a, i=i)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

