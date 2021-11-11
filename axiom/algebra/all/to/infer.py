from util import *


@apply(given=None)
def apply(given, *, simplify=True):
    fn1, *limits = given.of(All)
    cond = given.limits_cond
    if simplify:
        cond = cond.simplify()
    return Equivalent(given, Infer(cond, fn1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.infer)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.infer)


if __name__ == '__main__':
    run()
# created on 2018-12-22
# updated on 2018-12-22
