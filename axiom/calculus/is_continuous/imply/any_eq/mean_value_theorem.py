from util import *


@apply
def apply(given):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)
    assert b >= a
    return Any(Equal(Integral(f, (z, a, b)), (b - a) * _f), (xi, a, b))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval(a, oo, left_open=True))
    assert b > a
    assert b - a > 0
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    z = Eq[0].lhs.args[1][0]
    m = Symbol(Minima[z:a:b](f(z)))
    M = Symbol(Maxima[z:a:b](f(z)))
    Eq.min = m.this.definition

    Eq.max = M.this.definition

    Eq << calculus.all_eq.imply.all_any_eq.intermediate_value_theorem.apply(Eq[0])

    Eq.intermediate_value = Eq[-1].this.limits[0][2].subs(Eq.max.reversed).this.limits[0][1].subs(Eq.min.reversed)

    Eq << algebra.imply.all_le.minima.apply(m.definition)

    Eq << calculus.all_le.imply.le.integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)

    Eq << algebra.imply.all_ge.maxima.apply(M.definition)

    Eq << calculus.all_ge.imply.ge.integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)

    Eq <<= sets.le.ge.imply.el.interval.apply(Eq[-4], Eq[-1])

    Eq << algebra.all.imply.ou.subs.apply(Eq.intermediate_value, Eq.intermediate_value.rhs, Eq[-1].lhs)

    Eq << algebra.ou.imply.any_ou.apply(Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << algebra.any_et.imply.et.any.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (b - a)

    Eq << Eq[-1].this.expr.rhs.ratsimp().reversed


if __name__ == '__main__':
    run()

# created on 2020-06-15
