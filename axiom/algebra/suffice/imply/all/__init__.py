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

    a, b, x, y = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Suffice((f(a) > x) & (f(b) > y), f(a, b) > g(x, y)), wrt=(a, b))

    Eq << Eq[0].this.apply(algebra.suffice.fold, index=1)

    Eq << algebra.suffice.imply.all.single_variable.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.suffice.imply.all.single_variable)


if __name__ == '__main__':
    run()

from . import single_variable
