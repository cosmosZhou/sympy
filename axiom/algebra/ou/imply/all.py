from util import *


@apply
def apply(given, pivot=0, wrt=None):
    [*conds] = given.of(Or)

    eq = conds.pop(pivot)

    if wrt is None:
        wrt = eq.wrt

    assert eq._has(wrt)

    cond = eq.invert()

    return ForAll[wrt:cond](given.func(*conds))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))

    f = Function.f(complex=True, shape=())
    g = Function.g(complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)

    Eq << Eq[0].apply(algebra.cond.imply.et.all, cond=Equal(x, y))

    Eq << sets.imply.all.complement.apply(y, x=x)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq << sets.ne.to.contains.apply(x, y)

    Eq << ForAll[x: Equal(Bool(Contains(x, Eq[2].limits[0][1])), 1)](Eq[2].function, plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << algebra.equivalent.cond.imply.cond.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

