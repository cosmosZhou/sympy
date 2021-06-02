from util import *

from axiom.discrete.combinatorics.permutation.mapping.Qu2v import predefined_symbols




@apply
def apply(n, u=None):
    Q, w, x = predefined_symbols(n)
    if u is None:
        u = Q.definition.variable
    return Unequal(Q[u], Q[u].etype.emptySet)


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n)
    i = Symbol.i(integer=True)
    Q, t = Eq[0].lhs.args
    _t = t.copy(domain=Range(0, n + 1))
    a = Symbol.a(Lamda[i:n + 1](i) @ Swap(n + 1, n, _t))
    Eq << a.this.definition

    Eq << a[n].this.definition.this.rhs.expand()

    Eq << discrete.matrix.elementary.swap.invariant.set_comprehension.definition.apply(a)

    Eq <<= Eq[-1] & Eq[-2]

    x = Eq[0].rhs.variable.base
    Eq << Exists[x[:n + 1]](Contains(x[:n + 1], Q[_t]), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << algebra.any.given.any.subs.apply(Eq[-1], x[:n + 1], a, simplify=None)

    Eq << algebra.any.given.cond.apply(Eq[-1])

    Eq << sets.any_contains.imply.is_nonemptyset.apply(Eq[-3])

    Eq << Eq[-1].forall((_t,))


if __name__ == '__main__':
    run()
