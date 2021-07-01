from util import *


@apply
def apply(self):
    from axiom.algebra.all.to.et.doit.setlimit import doit
    return Equal(self, doit(Cup, self))


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

    Eq << apply(Cup[i:{a, b, c, d}](x[i]))

    Eq << Equal(Cup[i:{a}](x[i]), x[a], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equal(Cup[i:{b}](x[i]), x[b], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cup[i:{c}](x[i]), x[c], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cup[i:{d}](x[i]), x[d], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

