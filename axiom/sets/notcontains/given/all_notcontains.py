from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    expr, *limits = S.of(Cup)
    return All(NotContains(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(integer=True, given=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(NotContains(x, Cup[k:n](A[k])))

    Eq << ~Eq[0]

    Eq << sets.contains.imply.any_contains.st.cup.apply(Eq[-1], simplify=None)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()