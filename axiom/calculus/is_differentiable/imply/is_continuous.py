from util import *


@apply
def apply(all_contains):
    ((fx, (x, d)), R), (x_, *domain) = all_contains.of(All[Element[Derivative]])
    if len(domain) == 2:
        domain = Interval(*domain)
    else:
        [domain] = domain

    assert R == Interval(-oo, oo)
    assert x == x_
    assert d == 1
    assert not domain.left_open and not domain.right_open
    a, b = domain.of(Interval)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    f = lambda t: fx._subs(x, t)
    return is_continuous(f, a, b, x=x)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a, b, x = Symbol(real=True)
    f = Function(real=True)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    Eq << apply(is_differentiable(f, a, b, open=False))

    xi = Symbol(domain=Interval(a, b))
    Eq << Element(Subs(Eq[0].expr.lhs, x, xi), Eq[0].expr.rhs, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.cond.given.all.apply(Eq[-1], xi)

    Eq << Eq[-2].this.lhs.apply(calculus.subs.to.limit)

    Eq << Element(Limit[x:xi](x - xi), Reals, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.mul.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << Eq[-1].this.lhs.simplify().reversed

    Eq << algebra.cond.imply.all.apply(Eq[-1], xi)


if __name__ == '__main__':
    run()
