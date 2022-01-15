from util import *


@apply
def apply(given, old, new):
    function, *limits = given.of(Any)
    assert len(limits) == 1
    limit = limits[0]
    assert len(limit) == 1
    _old = limits[0][0]
    assert old == _old
    assert old.domain in new.domain

    return Any[new](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    a, b, z = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, right_open=True))
    y = Symbol(domain=Interval(a, b))
    f = Function(shape=(), integer=True)

    Eq << apply(Any[x](f(x) > 0), x, y)

    Eq << Eq[1].limits_subs(y, z)

    Eq << algebra.any.given.any.subs.apply(Eq[-1], z, x)


if __name__ == '__main__':
    run()

# created on 2019-02-16
