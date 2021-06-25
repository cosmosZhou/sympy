from util import *


@apply
def apply(a):
    n = a.shape[0]

    i = Symbol.i(integer=True)

    p = Symbol.p(shape=(oo,), etype=dtype.integer)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), a.set_comprehension())))

    return All[p[:n]:P](Any[i:n](Equal(p[i], a[n - 1])))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(etype=dtype.integer, shape=(n,))
    Eq << apply(a)

    Eq << Eq[1].subs(Eq[0])

    Eq << algebra.imply.all.limits_assert.apply(Eq[-1].limits)

    Eq << Contains(a[n - 1], Eq[-1].rhs, plausible=True)

    Eq << Eq[-1].this.rhs.split(Slice[-1:])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.contains.imply.any_contains.st.cup)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

del basic
from . import basic
