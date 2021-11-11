from util import *


@apply
def apply(given):
    (((_x, ((w, i, j, _k), (___k, (__k, z_, n_)))), (k, z, n)), _S), (x, S) = given.of(All[Element[Lamda[Indexed[MatMul[Indexed, Lamda]]]]])
    assert S == _S
    assert n == S.etype.shape[0] == n_
    assert z == 0 == z_
    assert x == _x
    assert __k == k == _k == ___k

    (_n, __i, __j), (_j, *j_limits), (_i, *i_limits) = w.definition.of(Lamda[SwapMatrix])

    if j_limits:
        zero, n_1 = j_limits
        assert zero == 0 and n_1 == n - 1

    if i_limits:
        zero, n_1 = i_limits
        assert zero == 0 and n_1 == n - 1

    assert __i == _i == i and __j == _j == j
    assert _n == n

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(n))))

    return All[p[:n]:P, x:S](Element(Lamda[k:n](x[p[k]]), S))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n)
    x = Symbol(**S.element_symbol().type.dict)
    i, j, k = Symbol(integer=True)
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    Eq.swap, Eq.P_definition, Eq.w_definition, Eq.axiom = apply(All[x:S](Element(Lamda[k:n](x[(w[i, j] @ Lamda[k:n](k))[k]]), S)))

    Eq << discrete.lamda_indexed.to.matmul.swap.apply(x, w)

    Eq << Eq.swap.subs(Eq[-1])

    Eq << discrete.all_el.imply.all_el.swapn.permutation.apply(Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-04
# updated on 2020-09-04
