from util import *


@apply
def apply(given, wrt=None):
    cond, q = given.of(Suffice)
    if wrt is None:
        wrt = cond.wrt
    elif isinstance(wrt, tuple):
        eqs = cond.of(And)
        assert len(eqs) == len(wrt)
        limits = []
        wrt = {*wrt}
        for eq in eqs:
            [x] = eq.free_symbols & wrt
            limits.append((x, eq))
        return All(q, *limits)
    return All[wrt:cond](q)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Suffice(x > y, f(x) > g(y)))

    Eq << algebra.suffice.imply.ou.apply(Eq[0])

    Eq << Eq[-1].apply(algebra.ou.imply.all, pivot=1)


if __name__ == '__main__':
    run()
