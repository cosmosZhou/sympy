from util import *


@apply
def apply(any_eq, forall, reverse=False):
    (x, y), *limits = any_eq.of(Any[Equal])
    cond, *_limits = forall.of(All)
    assert limits == _limits

    if reverse:
        x, y = y, x
    return Any(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    S = Symbol(etype=dtype.integer)

    Eq << apply(Any[x:S](Equal(g(x), f(x))), All[x:S](g(x) > y))

    Eq << algebra.all.any.imply.any_et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()

