from util import *

import axiom


@apply
def apply(given, old, new):
    function, *limits = given.of(ForAll)

    var, domain = axiom.limit_is_set(limits)
    assert len(given.variables) == 1
    assert old.is_Slice and old == var
    assert given.is_ForAll
    assert new.is_Slice and new.base.is_symbol and new.base.is_given is None

    return ForAll[new:domain](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n]:CartesianSpace(Interval(a, b), n)](f(x[:n]) > 0), x[:n], x[1:n + 1])

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << algebra.all.given.ou.apply(Eq[1])


if __name__ == '__main__':
    run()

