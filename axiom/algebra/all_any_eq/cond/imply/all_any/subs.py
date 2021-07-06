from util import *


@apply
def apply(all_any, cond, reverse=False):
    assert not cond.is_ConditionalBoolean
    (fn, *limits_e), *limits_f = all_any.of(All[Any])

    x, y = fn.of(Equal)
    if reverse:
        x, y = y, x

    return All(Any(cond._subs(x, y), *limits_e), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(All[y:B](Any[x:A](Equal(g(x, y), f(x, y)))), g(x, y) > y)

    Eq << algebra.cond.all.imply.all_et.apply(Eq[1], Eq[0])

    Eq << Eq[-1].this.function.apply(algebra.any_eq.cond.imply.any.subs)


if __name__ == '__main__':
    run()
