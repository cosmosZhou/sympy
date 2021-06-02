from util import *


@apply
def apply(*given, i=None, j=None):
    nonoverlapping, x_equal = given
    a_set_comprehension, n = nonoverlapping.of(Equal[Abs])
    (xk, limit), _a_set_comprehension = x_equal.of(Equal[Cup[FiniteSet]])
    x = Lamda(xk, limit).simplify()
    assert x.shape == (n,)
    
    assert _a_set_comprehension == a_set_comprehension
        
    ak, limit = a_set_comprehension.of(Cup[FiniteSet])
    a = Lamda(ak, limit).simplify()
    assert a.shape == (n,)
    
    if j is None:
        j = Symbol.j(domain=Range(0, n), given=True)

    if i is None:
        i = Symbol.i(domain=Range(0, n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove(surmountable=False)
def prove(Eq):

    n = Symbol.n(domain=Range(2, oo))

    x = Symbol.x(shape=(oo,), integer=True)
    
    a = Symbol.a(shape=(oo,), integer=True)

    k = Symbol.k(integer=True)

    j = Symbol.j(domain=Range(0, n), given=True)
    i = Symbol.i(domain=Range(0, n), given=True)

    Eq << apply(Equal(abs(a[:n].set_comprehension(k)), n),
                Equal(x[:n].set_comprehension(k), a[:n].set_comprehension(k)),
                i=i, j=j)


if __name__ == '__main__':
    run()

