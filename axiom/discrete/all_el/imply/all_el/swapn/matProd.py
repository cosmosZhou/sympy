from util import *


@apply
def apply(given, m=None, b=None):
    ((x, (w, i, j)), S), (_x, _S) = given.of(All[Element[MatMul[Indexed]]])
    assert S == _S and x == _x

    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    if m is None:
        m = Symbol(integer=True, nonnegative=True)

    if b is None:
        b = Symbol(integer=True, shape=(oo,))

    return All[x:S](Element(x @ MatProduct[i:m](w[i, b[i]]), S))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, nonnegative=True, given=False)
    S = Symbol(etype=dtype.integer * n, given=True)
    x = Symbol(shape=(n,), integer=True)
    i, j = Symbol(integer=True)
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    given = All[x[:n]:S](Element(x[:n] @ w[i, j], S))
    Eq.swap, Eq.w_definition, Eq.hypothesis = apply(given, m=m)

    i, _, m = Eq.hypothesis.expr.lhs.args[1].limits[0]
    b = Eq.hypothesis.expr.lhs.args[1].expr.indices[1].base
    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    Eq << Eq.induct.expr.lhs.args[1].this.apply(discrete.matProd.to.matmul.pop_back)

    Eq << x @ Eq[-1]

    Eq << Eq.swap.subs(i, m).subs(j, b[m])

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], x, Eq[1].rhs.func(*Eq[1].rhs.args[:2]))

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (x, S))

    Eq <<= Eq[-1] & Eq.hypothesis

    Eq << algebra.all_et.imply.all.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[1].reversed)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=m)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-03
