from util import *


@apply
def apply(*given, reverse=False):
    any_eq, forall = given

    (x, y), *limits = any_eq.of(Exists[Equal])
    cond, *_limits = forall.of(ForAll)
    assert limits == _limits

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

    Eq << apply(Exists[x:S](Equal(g(x), f(x))), ForAll[x:S](g(x) > y))

    Eq << algebra.all.any.imply.any_et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()

