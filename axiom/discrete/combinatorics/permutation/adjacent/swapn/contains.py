from util import *


@apply
def apply(given):
    assert given.is_ForAll
    S = given.rhs
    n = S.etype.shape[0]

    ref = given.lhs
    k = ref.variable
    x = ref.function.base

    assert len(ref.function.indices) == 1
    index = ref.function.indices[0]
    assert index.is_MatMul and len(index.args) == 2

    assert index.args[0].is_Indexed and index.args[1].is_Lamda

    w = index.args[0].base
    i, j, _k = index.args[0].indices

    assert w.definition.is_Lamda

    (_j, *j_limits), (_i, *i_limits) = w.definition.limits
    if j_limits:
        zero, n_1 = j_limits
        assert zero.is_zero and n_1 == n - 1

    if i_limits:
        zero, n_1 = i_limits
        assert zero.is_zero and n_1 == n - 1

    assert _k == k and _i == i and _j == j
    assert isinstance(w.definition.function, Swap)
    _n, _i, _j = w.definition.function.args
    assert _n == n and _i == i and _j == j

    assert index.args[1].is_Lamda and len(index.args[1].limits) == 1

    _k, *_ = index.args[1].limits[0]
    assert _k == k

    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))

    return ForAll[p[:n]:P, x:S](Contains(Lamda[k:n](x[p[k]]), S))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(domain=Range(2, oo))
    S = Symbol.S(etype=dtype.integer * n)

    x = Symbol.x(**S.element_symbol().type.dict)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    k = Symbol.k(integer=True)

    given = ForAll[x:S](Contains(Lamda[k:n](x[(w[i, j] @ Lamda[k:n](k))[k]]), S))

    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)

    Eq << discrete.matrix.elementary.swap.identity.apply(x, w)

    Eq << Eq.swap.subs(Eq[-1])

    Eq << discrete.combinatorics.permutation.adjacent.swapn.permutation.apply(Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
