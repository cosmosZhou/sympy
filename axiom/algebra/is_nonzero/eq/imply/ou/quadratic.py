from util import *
import axiom


@apply
def apply(*given, x=None):
    from axiom.algebra.ge.le.imply.le.quadratic import quadratic_coefficient
    is_nonzero, eq = given
    if not is_nonzero.is_Unequal:
        is_nonzero, eq = eq, is_nonzero

    a = is_nonzero.of(Unequal[0])
    fx, rhs = eq.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    _a, b, c = quadratic_coefficient(fx, x=x)
    assert a == _a
    delta = b * b - 4 * a * c

    return Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(complex=True, given=True)
    b = Symbol.b(complex=True, given=True)
    c = Symbol.c(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 2 + b * x + c, 0), x=x)

    x = Symbol.x(x + b / (2 * a))
    Eq << x.this.definition

    Eq << Eq[-1] - b / (2 * a)

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.is_nonzero.eq.imply.ou.square.apply(Eq[0], Eq[-1].reversed, x=x)

    Eq << Eq[-1].subs(x.this.definition)

    Eq << Eq[-1].this.args[0] - b / (2 * a)

    Eq << Eq[-1].this.args[0] - b / (2 * a)

    Eq << Eq[2].this.args[0].rhs.expand()

    Eq << Eq[-1].this.args[0].rhs.expand()


if __name__ == '__main__':
    run()