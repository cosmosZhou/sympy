from util import *


@apply
def apply(given):
    ((((x0, condition0), (xj, conditionj), (xi, conditioni)), (i, z, _n)), _S), (j, a, n), (x, S) = given.of(All[Element[Lamda[Piecewise]]])
    assert a == 1
    assert S == _S and S.is_set
    dtype = S.etype

    assert _n == n and z == 0

    assert {*condition0.of(Equal)} == {i, j}
    assert {*conditionj.of(Equal)} == {i, 0}
    assert conditioni

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    return All(Element(w[i, j] @ x, S), (x, S))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n)
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    Eq << apply(All(Element(Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S), (j, 1, n), (x, S)))

    w = Eq[1].lhs.base
    Eq << discrete.indexed.to.piece.swap1.helper.apply(x, w[0])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n), simplify=False)

    Eq.given = Eq[0].subs(Eq[-1].reversed)

    Eq << discrete.lamda_indexed.to.matmul.swap.apply(x, w)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].indices[0], 0)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, i)

    Eq << Eq[-1].this.lhs.expr.indices[0].args[1].limits_subs(Eq[-1].lhs.expr.indices[0].args[1].variable, i)

    Eq.given = Eq.given.subs(Eq[-1])

    Eq << algebra.all.imply.all.limits.swap.apply(Eq.given)

    Eq << All[x:S](Eq[-1].expr._subs(j, 0), plausible=True)

    Eq << Eq[-1].subs(w[0, 0].this.definition)

    Eq << Eq[-1].simplify()

    Eq << algebra.all.all.imply.all_et.apply(Eq[-2], Eq[-3])

    Eq << discrete.all_el.imply.all_el.swap2.apply(Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-12
