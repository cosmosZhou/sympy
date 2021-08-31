from util import *


@apply
def apply(x, w=None, right=None, var=None):
    n = x.shape[0]
    i, j = Symbol(integer=True)
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    if right:
        lhs = (x @ w[i, j]).set_comprehension(var=var)
    else:
        lhs = (w[i, j] @ x).set_comprehension(var=var)
    return Equal(lhs, x.set_comprehension(var=var))


@prove
def prove(Eq):
    from axiom import discrete, sets

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices
    k = Eq[1].lhs.variable.copy(domain=Range(0, n))
    Eq << Eq[0].lhs[k].this.definition

    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].apply(sets.eq.imply.eq.set_comprehension, (k, 0, n))

    Eq << Eq[-1].this.find(Complement[Complement]).apply(sets.complement.to.union.intersect)

    Eq << Eq[-1].this(i, j).find(Unequal, Intersection).simplify()

    Eq << Eq[-1].this(i, j).find(NotSubset, Intersection).simplify()

    Eq << Eq[-1].this(i, j).find(Element[Intersection]).simplify()

    Eq << Eq[-1].this(i, j).find(Intersection).simplify()

    Eq << Eq[-1].this.rhs.args[1]().expr.find(Intersection).simplify()

    Eq << Eq[-1].this.lhs.apply(sets.cup.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, i)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.domain_defined.insert)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

