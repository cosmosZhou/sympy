from util import *


@apply
def apply(nonoverlapping, x_equal, i=None, j=None):
    a_cup_finiteset, n = nonoverlapping.of(Equal[Card])
    (xk, limit), _a_cup_finiteset = x_equal.of(Equal[Cup[FiniteSet]])
    x = Lamda(xk, limit).simplify()
    [_n] = x.shape
    assert n == _n

    assert _a_cup_finiteset == a_cup_finiteset

    ak, limit = a_cup_finiteset.of(Cup[FiniteSet])
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

    Eq << apply(Equal(Card(a[:n].cup_finiteset(k)), n),
                Equal(x[:n].cup_finiteset(k), a[:n].cup_finiteset(k)),
                i=i, j=j)


if __name__ == '__main__':
    run()

# created on 2021-09-25
