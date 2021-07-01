from util import *


@apply
def apply(all_historic, all_n):
    if len(all_historic.limits) == 1:
        all_historic, all_n = all_n, all_historic

    (lhs, rhs), (j, _zero, i_1), (_i, zero, n_1) = all_historic.of(All[Unequal])
    if lhs._has(j):
        lhs, rhs = rhs, lhs

    assert zero == _zero == 0

    (_lhs, _rhs), (i, zero, _n_1) = all_n.of(All[Unequal])
    if _lhs._has(i):
        _lhs, _rhs = _rhs, _lhs

    assert i == i_1
    assert zero == 0
    assert _n_1 == n_1
    n = n_1

    x = Lamda[i:n + 1](lhs)
    assert x[j] == rhs

    assert x[n] == _lhs
    assert x[i] == _rhs

    return All[j:i, i:n + 1](Unequal(x[i], x[j]))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])),
                All[i:n](Unequal(x[n], x[i])))

    Eq << algebra.all.given.et.apply(Eq[-1], cond={n}, wrt=i)

    


if __name__ == '__main__':
    run()

