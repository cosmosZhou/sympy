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
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))

    f = Function.f(complex=True, shape=())
    g = Function.g(complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)

    Eq << algebra.all.imply.ou.apply(Eq[1])


if __name__ == '__main__':
    run()

