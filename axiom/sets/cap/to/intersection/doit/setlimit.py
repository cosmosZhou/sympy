from util import *


@apply
def apply(self):
    from axiom.algebra.all.to.et.doit.setlimit import doit
    assert self.is_Cap
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(etype=dtype.real, shape=(oo,))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Cap[i:{a, b, c, d}](x[i]))

    Eq << Equal(Cap[i:{a}](x[i]), x[a], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equal(Cap[i:{b}](x[i]), x[b], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.intersection.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[i:{c}](x[i]), x[c], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.intersection.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[i:{d}](x[i]), x[d], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.intersection.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

