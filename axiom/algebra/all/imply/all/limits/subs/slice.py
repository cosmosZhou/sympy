from util import *


@apply
def apply(given, old, new):
    function, (var, domain) = given.of(All)

    assert len(given.variables) == 1
    assert old.is_Slice and old == var
    assert new.is_Slice and new.base.is_symbol and new.base.is_given is None

    return All[new:domain](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)

    a, b = Symbol(real=True)
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True)

    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n)](f(x[:n]) > 0), x[:n], x[1:n + 1])

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << algebra.all.given.ou.apply(Eq[1])


if __name__ == '__main__':
    run()

