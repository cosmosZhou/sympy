from util import *


@apply
def apply(is_nonzero, eq, x=None):
    from axiom.algebra.ge.le.imply.le.quadratic import quadratic_coefficient
    if not is_nonzero.is_Unequal:
        is_nonzero, eq = eq, is_nonzero

    a = is_nonzero.of(Unequal[0])
    fx, rhs = eq.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    _a, b, c = quadratic_coefficient(fx, x=x)
    assert b.is_Zero
    assert a == _a
    delta = -4 * a * c

    return Or(Equal(x, sqrt(delta) / (a * 2)), Equal(x, -sqrt(delta) / (a * 2)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(complex=True, given=True)
    c = Symbol.c(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 2 + c, 0), x=x)

    Eq << Eq[1] - c

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])

    t = Symbol.t(sqrt(-c / a))
    Eq << t.this.definition

    Eq.t_squared = Eq[-1] ** 2

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq.t_squared)

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].reversed

    Eq.ou = Eq[-1].this.args[0] - t

    Eq << -Eq.t_squared * a

    Eq << Eq[-1].reversed

    Eq << Eq[2].subs(Eq[-1])

    Eq << sqrt(a * a * t * t).this.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.ou.given.eq.abs.apply(Eq[-1])

    Eq << algebra.ou.imply.eq.abs.apply(Eq.ou)


if __name__ == '__main__':
    run()
