from util import *


@apply
def apply(given):
    (lhs, _S), (x, S) = given.of(All[Element])

    assert S == _S

    w = lhs.args[0].base
    _, j = lhs.args[0].indices
    i = Symbol(integer=True)

    return All[x:S](Element(w[i, j] @ x, S))


@prove
def prove(Eq):
    from axiom import algebra, discrete, sets

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n)
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    w = Symbol(Lamda[j:n, i:n](SwapMatrix(n, i, j)))
    Eq << apply(All[x:S](Element(w[0, j] @ x, S)))

    j_ = j.copy(domain=Range(n))
    Eq.given = Eq[0].subs(j, j_)

    i_ = i.copy(domain=Range(n))
    Eq.given_i = Eq.given.subs(j_, i_)

    Eq << algebra.all.imply.ou.subs.apply(Eq.given, x, Eq.given_i.expr.lhs)

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq.given_i)

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=-1)

    Eq << algebra.all.imply.ou.subs.apply(Eq.given_i, x, Eq[-1].expr.lhs)

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-2], Eq[-1])

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq.final_statement = algebra.cond.imply.all.restrict.apply(Eq[-1], (i_,), (j_,))

    Eq << discrete.eq_lamda_swapMatrix.imply.all_eq.swap2.eq.apply(w.this.definition)

    Eq << Eq[-1].this.expr @ x

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (Eq[-1].limits[0].args[1].args[1].arg,))

    Eq << algebra.all.all.imply.all_et.apply(Eq.final_statement, Eq[-1])

    Eq.i_complement = Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq.plausible = All(Element(w[i, j] @ x, S), (x, S), (j, Range(1, n)), plausible=True)

    Eq << algebra.all.given.et.apply(Eq.plausible, cond=i.set, wrt=j)

    Eq << sets.imply.eq.intersect.apply(i, Range(1, n))

    Eq << Eq[-2].this.limits[1].subs(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.all.doit.outer.setlimit)

    Eq << Eq[-1].subs(w[i, i].this.definition).simplify()

    Eq << discrete.swapMatrix.swap.apply(w).subs(j, 0)

    Eq.given_i = algebra.cond.imply.all.restrict.apply(Eq.given_i, (i_,))

    Eq << Eq.given_i.subs(Eq[-1].reversed)

    Eq << algebra.all.given.et.apply(Eq[2], cond=Equal(j, 0))

    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2022-04-01
