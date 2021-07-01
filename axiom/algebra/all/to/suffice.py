from util import *


@apply(given=None)
def apply(given, *, simplify=True):
    fn1, *limits = given.of(All)
    cond = given.limits_cond
    if simplify:
        cond = cond.simplify()
    return Equivalent(given, Suffice(cond, fn1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.suffice)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.suffice)


if __name__ == '__main__':
    run()
