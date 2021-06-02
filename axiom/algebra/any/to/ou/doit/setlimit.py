from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.all.to.et.doit.setlimit import doit
    assert self.is_Exists
    return Equivalent(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Exists[i:{a, b, c, d}](x[i] > 0))

    Eq << Equivalent(Exists[i:{a}](x[i] > 0), x[a] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equivalent(Exists[i:{b}](x[i] > 0), x[b] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(Exists[i:{c}](x[i] > 0), x[c] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(Exists[i:{d}](x[i] > 0), x[d] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

