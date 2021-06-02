from util import *
import axiom



@apply
def apply(given):
    fn1, *limits = given.of(ForAll)
    return Suffice(given.limits_cond.simplify(), fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(ForAll[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Eq[1].this.apply(algebra.suffice.to.all, wrt=n)


if __name__ == '__main__':
    run()
