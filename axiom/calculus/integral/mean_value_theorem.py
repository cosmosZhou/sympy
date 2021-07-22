from util import *


@apply
def apply(given):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)

    return Any(Equal(Integral(f, (z, a, b)), (b - a) * _f), (xi, a, b))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True, domain=Interval(a, oo, left_open=True))
    assert b > a
    assert b - a > 0
    f = Function.f(shape=(), real=True)
    given = calculus.integral.intermediate_value_theorem.is_continuous(f, a, b)
    z = given.lhs.args[1][0]
    Eq << apply(given)

    m = Symbol.m(Minimize[z:a:b](f(z)))
    M = Symbol.M(Maximize[z:a:b](f(z)))
    Eq.min = m.this.definition

    Eq.max = M.this.definition

    Eq << calculus.integral.intermediate_value_theorem.apply(given)

    Eq.intermediate_value = Eq[-1].this.limits[0][2].subs(Eq.max.reversed).this.limits[0][1].subs(Eq.min.reversed)

    Eq << algebra.imply.all_le.min.apply(m.definition)

    Eq << algebra.all_le.imply.le.integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)

    Eq << algebra.imply.all_ge.max.apply(M.definition)

    Eq << calculus.all_ge.imply.ge.integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)

    Eq <<= sets.le.ge.imply.contains.interval.apply(Eq[-4], Eq[-1])

    Eq << algebra.all.imply.ou.subs.apply(Eq.intermediate_value, Eq.intermediate_value.rhs, Eq[-1].lhs)

    Eq << algebra.ou.imply.any_ou.apply(Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << algebra.any_et.imply.et.any.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (b - a)

    Eq << Eq[-1].this.expr.rhs.ratsimp().reversed


if __name__ == '__main__':
    run()

