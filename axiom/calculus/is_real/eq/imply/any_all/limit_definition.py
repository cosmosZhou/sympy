from util import *


@apply
def apply(is_real, given, epsilon=None, delta=None):
    _a, R = is_real.of(Contains)
    assert R == Reals
    l, a = given.of(Equal)
    if a.is_Limit:
        l, a = a, l
    assert a == _a
    _a = l.generate_var(excludes=l.variable, real=True)
    given = given._subs(a, _a)
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    given = any_all(given, epsilon, delta)
    return given._subs(_a, a)


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True, shape=())
    x0 = Symbol.x0(real=True)
    a = Symbol.a(complex=True)
    direction = 1
    Eq << apply(Contains(a, Reals), Equal(Limit[x:x0:direction](f(x)), a))

    Eq << sets.contains.imply.any_eq.apply(Eq[0], var='A')

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.invoke, algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.expr.args[1].apply(calculus.eq.imply.any_all.limit_definition)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()