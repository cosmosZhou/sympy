from util import *


@apply
def apply(n):
    assert n > 0
    x = Symbol.x(integer=True, nonnegative=True, shape=(oo,))
    P = Symbol("P", conditionset(x[:n], Equal(x[:n].set_comprehension(), Range(0, n))))
    return Unequal(P, P.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n)

    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    Eq << Any[x[:n]](Contains(x[:n] , P), plausible=True)

    Eq << sets.any_contains.imply.is_nonemptyset.apply(Eq[-1])

    Eq << Eq[-1].this.function.rhs.definition

    i = Symbol.i(integer=True)

    Eq << algebra.any.given.cond.subs.apply(Eq[-1], x[:n], Lamda[i:n](i))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
