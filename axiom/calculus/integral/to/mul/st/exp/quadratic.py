from util import *


def coefficient(y, x):
    quadratic = -log(y.powsimp()).simplify()
    quadratic = quadratic.as_poly(x)
    if quadratic.degree() != 2:
        return None
    b = quadratic.coeff_monomial(x)
    a = quadratic.coeff_monomial(x * x)
    c = quadratic.coeff_monomial(1)
    return a, b, c


def doit(a, b, c):
    delta = (b ** 2) / (4 * a) - c
#     delta = (b ** 2 - 4 * a * c) / (4 * a)
    delta = delta.ratsimp()

    return sqrt(pi) * exp(delta) / sqrt(a)


@apply
def apply(y):

    if not isinstance(y, Integral):
        print('not isinstance(y, Integral)')
        return

    if len(y.limits) > 1:
        return

    (x, *ab), *_ = y.limits

    if ab:
        if a != -oo or b != oo:
            return

    a, b, c = coefficient(y.expr, x)
    if a <= 0:
        return

    return Equal(y, doit(a, b, c))


@prove
def prove(Eq):
    from axiom import calculus, algebra, stats

    a = Symbol(positive=True)
    b, c, x = Symbol(real=True)
    Eq << apply(Integral[x](exp(-(a * x * x + b * x + c))))

    Eq << Eq[0].this.lhs.apply(calculus.integral.limits.offset, - b / (2 * a))

    Eq << Eq[-1].this.lhs.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.domain_defined.insert)

    Eq << stats.imply.eq.guassion.std.apply()

    Eq << Eq[-1] * sqrt(2 * pi)

    Eq << Eq[-1].this.lhs.limits_subs(x, sqrt(2 * a) * x)

    Eq << Eq[-1] / sqrt(a)


if __name__ == '__main__':
    run()

# created on 2020-06-11
