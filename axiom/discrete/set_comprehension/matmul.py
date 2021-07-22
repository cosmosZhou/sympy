from util import *


@apply
def apply(a, var=None, *, simplify=True):
    matmul = a.definition
    lhs, rhs = matmul.of(MatMul)

    if lhs.is_Swap:
        w = lhs
        x = rhs
    elif rhs.is_Swap:
        w = rhs
        x = lhs
    else:
        return
    a = a.set_comprehension(var=var)
    x = x.set_comprehension(var=var)
    if simplify:
        a = a.simplify()
        x = x.simplify()
    return Equal(a, x)


@prove
def prove(Eq):
    from axiom import discrete, sets

    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)
    a = Symbol.a(x @ Swap(n, i, j))
    Eq << apply(a, var=k)

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    Eq << w[i, j].this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << discrete.set_comprehension.rmatmul.apply(x, w, right=True, var=k)

    Eq << Eq[-2][k]

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.domain_defined.delete)

    Eq << Eq[-1].this.lhs.apply(sets.cup.limits.domain_defined.delete)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
