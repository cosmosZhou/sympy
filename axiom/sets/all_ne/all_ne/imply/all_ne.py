from util import *

# given:
#     ForAll[j:Range(0, n) - {i}, i:n](Unequal(x[i], x[j]))
#     ForAll[i:n](Unequal(x[n], x[i])))

# ForAll[j:Range(0, n + 1) - {i}, i:n+1](Unequal(x[i], x[j]))


@apply
def apply(*given):
    all_historic, all_n = given
    assert all_historic.is_ForAll and all_n.is_ForAll

    if len(all_historic.limits) == 1:
        all_historic, all_n = all_n, all_historic
    (j, _zero, i_1), (_i, zero, n_1) = all_historic.limits
    assert zero.is_zero and _zero.is_zero

    assert len(all_n.limits) == 1
    i, zero, _n_1 = all_n.limits[0]
    assert i == i_1
    assert zero.is_zero
    assert _n_1 == n_1
    n = n_1

    assert all_historic.function.is_Unequal and all_n.function.is_Unequal
    lhs, rhs = all_historic.function.args
    if lhs._has(j):
        lhs, rhs = rhs, lhs
    x = Lamda[i:n + 1](lhs)
    assert x[j] == rhs

    lhs, rhs = all_n.function.args
    if lhs._has(i):
        lhs, rhs = rhs, lhs

    assert x[n] == lhs
    assert x[i] == rhs

    return ForAll[j:i, i:n + 1](Unequal(x[i], x[j]))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)

    Eq << apply(ForAll[j:i, i:n](Unequal(x[i], x[j])),
                ForAll[i:n](Unequal(x[n], x[i])))

    Eq << algebra.all.given.et.apply(Eq[-1], cond={n}, wrt=i)

    Eq << algebra.et.given.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

