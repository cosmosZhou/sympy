from util import *


@apply
def apply(equivalent, condition):
    fn, fn1 = equivalent.of(Equivalent)
    return condition._subs(fn, fn1)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g, h = Symbol(integer=True, shape=(oo,))
    Eq << apply(Equivalent(f[n] > 0, g[n] > 0), All[n:f[n] > 0](h[n] > 0))

    Eq << algebra.iff.imply.eq.apply(Eq[0])

    Eq << All[n:Equal(Bool(f[n] > 0), 1)](h[n] > 0, plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.limits[0][1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()
# created on 2018-03-23
