from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.all.doit.inner.setlimit import doit
    assert self.is_Exists
    return Equivalent(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Exists[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Equivalent(Exists[i:m](Equal(Bool(Exists[j:{a, b, c, d}](x[i, j] > 0)), 1)), Exists[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Bool, Exists).apply(algebra.any.to.ou.doit.setlimit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

