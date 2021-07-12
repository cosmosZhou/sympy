from util import *


@apply
def apply(given, pivot=0, wrt=None):
    [*conds] = given.of(Or)

    eq = conds.pop(pivot)

    if wrt is None:
        wrt = eq.wrt

    assert eq._has(wrt)

    cond = eq.invert()

    return All[wrt:cond](given.func(*conds))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,), given=True)
    f = Function.f(complex=True, shape=())
    g = Function.g(complex=True, shape=())
    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)

    Eq << ~Eq[-1]

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1])














if __name__ == '__main__':
    run()

