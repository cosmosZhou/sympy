from util import *


@apply
def apply(given):
    (((w, i, j), x), S), (_x, _S) = given.of(All[Contains[MatMul[Indexed]]])

    assert x == _x and S == _S

    n = S.etype.shape[0]

    k = Symbol.k(integer=True)

    assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))

    return All[p[:n]:P, x:S](Contains(Lamda[k:n](x[p[k]]), S))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo))
    S = Symbol.S(etype=dtype.integer * n, given=True)

    x = Symbol.x(shape=(oo,), integer=True)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(All[x[:n]:S](Contains(w[i, j] @ x[:n], S)))

    Eq << discrete.combinatorics.permutation.adjacent.factorization.apply(n)

    * _, b_i = Eq[-1].rhs.args[1].function.args
    b, _i = b_i.args
    Eq << Eq.w_definition.subs(j, b[_i])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    k = Eq.axiom.lhs.variable
    Eq << Eq[-1][k]

    Eq << Eq[-1].this.function.function.rhs.args[0].limits_subs(_i, k)

    Eq << discrete.combinatorics.permutation.adjacent.swapn.helper.apply(x[:n], b[:n], w)

    Eq << algebra.all_any_eq.cond.imply.all_any.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], (x[:n], S))

    Eq <<= Eq[-1] & Eq.axiom

    Eq << Eq[-1].this.function.apply(algebra.et.given.any_et, simplify=None)

    Eq << Eq[-1].this.function.function.apply(algebra.et.given.et.subs.eq)

    Eq << Eq[-1].this.function.apply(algebra.any_et.given.et, index=-1)

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << discrete.combinatorics.permutation.adjacent.swapn.mat_product.apply(Eq.swap.T, n, b)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
