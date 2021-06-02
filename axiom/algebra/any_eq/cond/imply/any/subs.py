from util import *


@apply
def apply(*given, reverse=False):
    any_eq, cond = given
    if not any_eq.is_Exists:
        any_eq, cond = cond, any_eq

    assert not cond.is_ConditionalBoolean
    (x, y), *limits = any_eq.of(Exists[Equal])

    if reverse:
        x, y = y, x
    return Exists(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Exists[x:S](Equal(g(x), f(x))), g(x) > y)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()

