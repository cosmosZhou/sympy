from util import *


@apply
def apply(all_contains):
    ((fx, (x, d)), R), (x_, *domain) = all_contains.of(All[Contains[Derivative]])
    if len(domain) == 2:
        domain = Interval(*domain)
    else:
        [domain] = domain
        
    assert R == Interval(-oo, oo)
    assert x == x_
    assert d == 1
    assert not domain.left_open and not domain.right_open
    a, b = domain.of(Interval)
    from axiom.calculus.integral.intermediate_value_theorem import is_continuous
    f = lambda t: fx._subs(x, t)
    return is_continuous(f, a, b, x=x)


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    Eq << apply(is_differentiable(f, a, b, open=False))

    xi = Symbol.xi(domain=Interval(a, b), given=True)
    Eq << algebra.all.imply.cond.subs.apply(Eq[0], x, xi)

    Eq << Eq[-1].this.lhs.apply(calculus.subs.to.limit)

    Eq << sets.contains.imply.any_eq.apply(Eq[-1], var='k')
    Eq << Eq[-1].this.function * (x - xi)


if __name__ == '__main__':
    run()