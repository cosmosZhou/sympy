from util import *

import axiom



@apply
def apply(*given):
    equivalent, condition = given
    fn, fn1 = equivalent.of(Equivalent)
    return condition._subs(fn, fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))

    Eq << apply(Equivalent(f[n] > 0, g[n] > 0), ForAll[n:f[n] > 0](h[n] > 0))

    Eq << algebra.equivalent.imply.eq.apply(Eq[0])

    Eq << ForAll[n:Equal(Bool(f[n] > 0), 1)](h[n] > 0, plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.limits[0][1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()