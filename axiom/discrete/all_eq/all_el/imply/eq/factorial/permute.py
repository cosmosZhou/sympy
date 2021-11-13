from util import *


@apply
def apply(all0, all1):

    (ref, _S), (j, a, n_munis_1), (x, S) = all0.of(All[Element])
    assert a == 1

    piecewise, (i, _n_munis_1) = ref.of(Lamda[Tuple[0]])
    assert S == _S and S.is_set
    dtype = S.etype
    assert _n_munis_1 == n_munis_1

    (x0, condition0), (xj, conditionj), (xi, conditioni) = piecewise.of(Piecewise)
    assert condition0.is_Equal and {*condition0.args} == {i, j}
    assert conditionj.is_Equal and {*conditionj.args} == {i, 0}
    assert conditioni

    n = n_munis_1

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    equality, (_x, _S) = all1.of(All)
    assert x == _x and S == _S
    assert equality.is_Equal and {*equality.args} == {Card(x.set_comprehension()), n}

    return Equal(Card(S), factorial(n) * Card(Cup[x:S]({x.set_comprehension()})))


@prove(proved=False)
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n)
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    Eq << apply(All[j:1:n, x:S](Element(Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S)),
                All[x:S](Equal(Card(x.set_comprehension()), n)))

    Eq << discrete.eq.imply.eq.swap2.general.apply(Eq[0])

    Eq.permutation = discrete.all_el.imply.all_el.swapn.permutation.apply(Eq[-1])

    Eq << Eq.permutation.limits[0][1].this.definition

    Eq << discrete.abs_cup.to.factorial.apply(n)

    Eq << Eq[-1].this.lhs.arg.limits_subs(Eq[-1].lhs.arg.variable, Eq[-2].rhs.variable)

    Eq << Eq[-2].apply(sets.eq.imply.eq.card)

    Eq <<= Eq[-2] & Eq[-1]

    F = Function(etype=dtype.integer * n)
    F.eval = lambda e: conditionset(x, Equal(x.set_comprehension(), e), S)
    e = Symbol(etype=dtype.integer)
    Eq << Subset(F(e), S, plausible=True)

    Eq << Eq[-1].this.lhs.defun()

    Eq << sets.subset.all.imply.all.apply(Eq[-1], Eq.permutation)

    Eq.all_x = All(Element(Eq[-1].lhs, F(e)), *Eq[-1].limits, plausible=True)

    Eq << Eq.all_x.this.expr.rhs.defun()

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    P = Eq[-1].limits[0][1]
    Eq << sets.imply.all.conditionset.apply(P)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.eq.permutation, x)

    Eq.equality_e = Eq[-3] & Eq[-1]

    return
    Eq << sets.imply.all.conditionset.apply(F(e)).reversed
    hat_S = Symbol("\hat{S}", Eq[2].rhs.args[0].arg)
    Eq.hat_S_definition = hat_S.this.definition
    Eq << Equal(S, Cup[e:hat_S](F(e)), plausible=True)
    return
    Eq << Eq[-1].subs(Eq.hat_S_definition)
    Eq << Eq[-1].this.rhs.expr.definition


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-14
# updated on 2020-09-14