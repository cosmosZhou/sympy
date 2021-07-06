from util import *


@apply
def apply(given):
    ((((x0, condition0), (xj, conditionj), (xi, conditioni)), (i, z, _n)), _S), (j, a, n), (x, S) = given.of(All[Contains[Lamda[Piecewise]]])
    assert a == 1
    assert S == _S and S.is_set
    dtype = S.etype

    assert _n == n and z == 0

    assert {*condition0.of(Equal)} == {i, j}
    assert {*conditionj.of(Equal)} == {i, 0}
    assert conditioni

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    return All(Contains(w[i, j] @ x, S), (x, S))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(domain=Range(2, oo))
    S = Symbol.S(etype=dtype.integer * n)
    x = Symbol.x(**S.element_symbol().type.dict)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    given = All(Contains(Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S), (j, 1, n), (x, S))
    Eq << apply(given)

    w = Eq[0].lhs.base
    Eq << discrete.combinatorics.permutation.adjacent.swap1.helper.apply(x, w[0])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n), simplify=False)

    Eq.given = Eq[1].subs(Eq[-1].reversed)

    Eq << discrete.matrix.elementary.swap.identity.apply(x, w)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].indices[0], 0)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, i)

    Eq << Eq[-1].this.lhs.function.indices[0].args[1].limits_subs(Eq[-1].lhs.function.indices[0].args[1].variable, i)

    Eq.given = Eq.given.subs(Eq[-1])

    Eq << algebra.all.imply.all.limits.swap.apply(Eq.given)

    Eq << All[x:S](Eq[-1].function._subs(j, 0), plausible=True)

    Eq << Eq[-1].subs(w[0, 0].this.definition)

    Eq << Eq[-1].simplify()

    Eq << algebra.all.all.imply.all_et.apply(Eq[-2], Eq[-3])

    Eq << discrete.combinatorics.permutation.adjacent.swap2.contains.apply(Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
