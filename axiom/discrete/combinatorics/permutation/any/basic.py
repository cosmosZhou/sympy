from util import *



@apply
def apply(n):
    i = Symbol.i(integer=True)

    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))

    return All[p[:n]:P](Any[i:n](Equal(p[i], n - 1)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    Eq << Eq[1].subs(Eq[0])

    Eq << algebra.imply.all.limits_assert.apply(Eq[-1].limits)

    Eq << Contains(n - 1, Eq[-1].rhs, plausible=True)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.contains.imply.any_contains.st.cup)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
