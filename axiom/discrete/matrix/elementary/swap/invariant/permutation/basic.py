from util import *




@apply
def apply(n, w=None, left=True, P=None):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]

    if P is None:
        P = Symbol.P(conditionset(x, Equal(x.set_comprehension(), Range(0, n))))

    if left:
        return All[x:P](Contains(w[i, j] @ x, P))
    else:
        return All[x:P](Contains(x @ w[i, j], P))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(domain=Range(2, oo))

    Eq << apply(n)

    w = Eq[0].lhs.base

    x = Eq[2].variable

    Eq << discrete.matrix.elementary.swap.invariant.set_comprehension.cup.apply(x, w)

    Eq << Eq[2].this.function.rhs.definition.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
