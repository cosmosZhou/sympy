from util import *


@apply
def apply(given, piecewise, invert=None):
    assert given.is_NotContains

    piecewise.of(Piecewise)

    eq = given
    if invert:
        eq = eq.invert()
        assert piecewise._has(eq)
        return Equal(piecewise, piecewise._subs(eq, S.false))
    assert piecewise._has(eq)
    return Equal(piecewise, piecewise._subs(eq, S.true))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(NotContains(x, S), Piecewise((f(x), Contains(x, S)), (g(x), True)), invert=True)

    y = Symbol.y(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

