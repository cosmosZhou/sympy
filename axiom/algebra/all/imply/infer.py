from util import *


@apply
def apply(given, simplify=True):
    fn1, *limits = given.of(All)
    cond = given.limits_cond
    if simplify:
        cond = cond.simplify()
    return Infer(cond, fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Eq[1].apply(algebra.infer.given.ou)

    Eq << algebra.all.imply.ou.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-03-25
