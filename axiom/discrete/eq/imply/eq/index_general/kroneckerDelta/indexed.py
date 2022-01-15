from util import *


@apply
def apply(nonoverlapping, x_equal, i=None, j=None):
    a_set_comprehension, n = nonoverlapping.of(Equal[Card])
    (xk, limit), _a_set_comprehension = x_equal.of(Equal[Cup[FiniteSet]])
    x = Lamda(xk, limit).simplify()
    [_n] = x.shape
    assert n == _n

    assert _a_set_comprehension == a_set_comprehension

    ak, limit = a_set_comprehension.of(Cup[FiniteSet])
    a = Lamda(ak, limit).simplify()
    [_n] = a.shape
    assert n == _n


    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove(proved=False)
def prove(Eq):

    n = Symbol(domain=Range(2, oo))

    x, a = Symbol(shape=(oo,), integer=True)
    k = Symbol(integer=True)

    i, j = Symbol(domain=Range(n), given=True)

    Eq << apply(Equal(Card(a[:n].set_comprehension(k)), n),
                Equal(x[:n].set_comprehension(k), a[:n].set_comprehension(k)),
                i=i, j=j)


if __name__ == '__main__':
    run()

# created on 2021-09-25
