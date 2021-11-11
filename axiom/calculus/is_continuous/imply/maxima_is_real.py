from util import *


@apply
def apply(given):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)
    assert b >= a
    return Element(Maxima[z:a:b](f), Reals)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval(a, oo, left_open=True))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << calculus.is_continuous.imply.any_all_le.extreme_value_theorem.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.all_le.imply.le_maxima)

    Eq << algebra.imply.all_ge.maxima.apply(Eq[1].lhs)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[-2].variable)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[-2])

    Eq << Element(Eq[-1].expr.rhs, Reals, plausible=True)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-15
# updated on 2020-06-15
