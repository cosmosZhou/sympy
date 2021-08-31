from util import *



@apply
def apply(given):
    fn1, *limits = given.of(All)
    return Suffice(given.limits_cond.simplify(), fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Eq[1].this.apply(algebra.suffice.to.all, wrt=n)


if __name__ == '__main__':
    run()
