from util import *


@apply
def apply(given):
    (((w, i, j), x), S), (_x, _S) = given.of(All[Element[MatMul[Indexed]]])

    assert x == _x and S == _S

    n = S.etype.shape[0]

    k = Symbol(integer=True)

    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    return All[p[:n]:P, x:S](Element(Lamda[k:n](x[p[k]]), S))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n, given=True)
    x = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    Eq.swap, (Eq.P_definition, Eq.w_definition), Eq.axiom = apply(All[x[:n]:S](Element(w[i, j] @ x[:n], S)))

    Eq << discrete.imply.all_any.factorization.apply(n)

    * _, b_i = Eq[-1].rhs.args[1].expr.args
    b, _i = b_i.args
    Eq << Eq.w_definition.subs(j, b[_i])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    k = Eq.axiom.lhs.variable
    Eq << Eq[-1][k]

    Eq << Eq[-1].this.expr.expr.rhs.args[0].limits_subs(_i, k)

    Eq << discrete.lamda.to.matmul.swapn.helper.apply(x[:n], b[:n], w)

    Eq << algebra.all_any_eq.cond.imply.all_any.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], (x[:n], S))

    Eq <<= Eq[-1] & Eq.axiom

    Eq << Eq[-1].this.expr.apply(algebra.cond.any.given.any_et, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(algebra.et.given.et.subs.eq)

    Eq << Eq[-1].this.expr.apply(algebra.any_et.given.et, index=-1)

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << discrete.all_el.imply.all_el.swapn.matProd.apply(Eq.swap.T, n, b)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-03
