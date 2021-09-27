from util import *


@apply
def apply(is_nonnegative, self, offset):
    expr = is_nonnegative.of(Expr >= 0)
    _expr, (x, E) = self.of(Integral)
    assert _expr == expr
    E -= offset
    return Equal(self, Integral[x:E](expr._subs(x, x + offset)))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, a, b, d = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:Interval(a, b)](f(x)), d)

    Eq << calculus.is_nonnegative.imply.eq.integral.to.mul.limit.Lebesgue.apply(Eq[0], Eq[1].lhs)

    Eq << calculus.is_nonnegative.imply.eq.integral.to.mul.limit.Lebesgue.apply(Eq[0], Eq[1].rhs)

    Eq << Eq[-1].find(Sup).this.apply(algebra.sup.limits.subs.offset, -d)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.limits.subs.offset, -d)

    Eq << Eq[-1].this.find(Measure).apply(sets.measure.offset)

    Eq << Eq[-1].subs(Eq[2].reversed).reversed


if __name__ == '__main__':
    run()