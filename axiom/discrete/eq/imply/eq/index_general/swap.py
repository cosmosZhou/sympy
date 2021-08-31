from util import *


@apply
def apply(given, i=None, j=None, w=None):
    from axiom.discrete.eq.imply.et.index import index_function
    x_set_comprehension, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n
    x = Lamda(x_set_comprehension.expr.arg, *x_set_comprehension.limits).simplify()

    if j is None:
        j = Symbol.j(domain=Range(0, n), given=True)

    if i is None:
        i = Symbol.i(domain=Range(0, n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    index = index_function(n)
    if w is None:
        _i = Symbol.i(integer=True)
        _j = Symbol.j(integer=True)
        w = Symbol.w(Lamda[_j, _i](Swap(n, _i, _j)))

    return Equal(index[i](w[index[i](x[:n]), index[j](x[:n])] @ x[:n]), index[j](x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    k = Symbol(integer=True)
    j, i = Symbol(domain=Range(0, n), given=True)
    Eq << apply(Equal(x[:n].set_comprehension(k), Range(0, n)), i, j)

    _, di, dj = Eq[2].lhs.arg.args[0].args
    dj = Symbol("d_j", dj)
    di = Symbol("d_i", di)
    Eq.dj_definition = dj.this.definition

    Eq.di_definition = di.this.definition

    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)

    _i, _j = Eq[1].lhs.indices
    Eq << Eq[1].subs(_i, di).subs(_j, dj)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.definition = Eq[-1].this.lhs.defun()

    Eq.expand = Eq.definition.lhs.args[0].expr.args[1].this.apply(discrete.matmul.to.sum)

    Eq << discrete.eq.imply.et.index.apply(Eq[0], j=j)

    Eq.dj_domain, Eq.x_dj_eqaulity = Eq[-2].subs(Eq.dj_definition.reversed), Eq[-1].subs(Eq.dj_definition.reversed)

    Eq.expand = Eq.expand.subs(Eq.x_dj_eqaulity)

    Eq << discrete.eq.imply.et.index.apply(Eq[0], j=i)

    Eq.di_domain, Eq.x_di_eqaulity = Eq[-2].subs(Eq.di_definition.reversed), Eq[-1].subs(Eq.di_definition.reversed)

    Eq << sets.el.el.imply.subset.finiteset.apply(Eq.dj_domain, Eq.di_domain, simplify=False)
    Eq.eq_intersection = sets.subset.imply.eq.intersect.apply(Eq[-1])

    Eq << Eq.expand.subs(Eq.x_di_eqaulity)

    Eq.union_equality, Eq.piecewise_equality = sets.subset.imply.eq.union.apply(Eq[-2]), Eq.definition.subs(Eq[-1])

    Eq.piecewise_equality = Eq.piecewise_equality.this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq.piecewise_equality.lhs.args[-1].this.apply(algebra.sum.to.add.split.complement)


    Eq << Eq[-1].subs(Eq.eq_intersection)

    Eq << Eq[-1].subs(Eq.x_dj_eqaulity).subs(Eq.x_di_eqaulity)

    Eq << Eq[-1].this.rhs.subs(Eq.union_equality)

    Eq << Eq.di_definition.this.rhs.defun().this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.piecewise_equality = Eq.piecewise_equality.subs(Eq[-1])

    Eq.dj_eq = sets.el.imply.eq.piece.expr_swap.apply(Eq.dj_domain, Eq.piecewise_equality.lhs.args[2])

    Eq << sets.el.imply.eq.piece.expr_swap.apply(Eq.di_domain, Eq.piecewise_equality.lhs.args[-1])

    Eq << sets.el.imply.eq.intersect.apply(Eq.dj_domain)

    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.find(Element).simplify()

    Eq << Eq.dj_eq + Eq[-1]

    Eq << Eq.piecewise_equality.subs(Eq[-1])

    Eq << discrete.eq.imply.eq.index.kroneckerDelta.indexOf.apply(Eq[0], i, j)

    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)

    Eq << Eq[-3].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
