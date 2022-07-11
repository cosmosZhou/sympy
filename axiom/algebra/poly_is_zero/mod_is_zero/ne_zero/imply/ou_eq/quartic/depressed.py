from util import *


from axiom.algebra.poly_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
from axiom.algebra.ne_zero.poly_is_zero.imply.ne import cubic_delta


@apply
def apply(fx, mod_is_zero, is_nonzero, x=None):
    if fx.lhs.is_Mod:
        fx, mod_is_zero = mod_is_zero, fx

    from axiom.algebra.poly_is_zero.imply.et.infer.quartic.one_leaded import quartic_coefficient
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, beta, gamma = quartic_coefficient(fx, x=x)

    _d, d = mod_is_zero.of(Equal[Expr % 3])
    y_delta = cubic_delta(x, alpha, beta, gamma)
    S[_d], y0 = cubic_solve(y_delta, x, d)

    S[beta] = is_nonzero.of(Unequal[0])

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)
    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2
    if d == 0:
        y = A + B
    elif d % 3 == 1:
        y = A * w + B
    elif d % 3 == 2:
        y = A * ~w + B
    else:
        ...

    y0 = -2 * alpha / 3 + y
    y1 = 4 * alpha / 3 + y

    x0 = sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2
    x1 = -sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2
    x2 = sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2
    x3 = -sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2

    return Equal(x, x0) | Equal(x, x1) | Equal(x, x2) | Equal(x, x3)


@prove
def prove(Eq):
    from axiom import algebra

    d = 1
    x, y, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    y_delta = cubic_delta(y, alpha, beta, gamma)
    _d, y0 = cubic_solve(y_delta, y, d)
    Eq << apply(Equal(fx, 0), Equal(_d % 3, d), Unequal(beta, 0), x=x)

    y = Symbol(y0)
    Eq << y.this.definition

    Eq << ((x ** 2 + y) ** 2).this.apply(algebra.square.to.add)

    Eq << Eq[-1] + Eq[0]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq.eq = Eq[-1].this.apply(algebra.eq.transport, lhs=slice(0, 3))

    Eq << Equal(Eq[-1].rhs, 0).this.apply(algebra.poly_is_zero.imply.et.infer.quadratic, x)

    Eq << Equal(cubic_delta(y, alpha, beta, gamma), 0).this.apply(algebra.poly_is_zero.given.et_eq.mod.cubic.one_leaded, y, d=1)

    Eq << Eq[-1].subs(Eq[1])

    Eq << algebra.cond.assuming.imply.cond.transit.apply(Eq[4], Eq[-1], simplify=None)

    Eq << algebra.ne_zero.poly_is_zero.imply.ne.apply(Eq[2], Eq[-1], y)

    Eq << algebra.ne.imply.ne_zero.apply(Eq[-1]) * 2

    Eq << algebra.ne_zero.poly_is_zero.imply.eq.square.apply(Eq[-1], Eq[-3] * -8, Eq.eq.rhs)

    Eq << Eq.eq.subs(Eq[-1])

    Eq << algebra.eq_square.imply.ou_is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.poly_is_zero.imply.et.infer.quadratic)

    Eq.root = Eq[-1].this.args[-1].apply(algebra.poly_is_zero.imply.et.infer.quadratic)

    Eq << Eq[4] * 6

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.mul.to.pow.mul.base)

    Eq << (6 * Eq[-1].find(Mul[~Pow])).this.apply(algebra.mul.to.pow.mul.base)

    Eq.y = Eq[-2].subs(Eq[-1])

    Eq << Eq.y.find(Integer * Pow[S.One / 2]).this.apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Mul[Pow]).apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Mul[Pow]).apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Expr ** 3).apply(algebra.pow.to.mul.neg)

    Eq << Eq.y.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.div.apply(Eq[-1], 3)

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.mul.to.pow.mul.base)

    Eq << (Eq[-1].find(Mul[~Pow]) / 3).this.apply(algebra.mul.to.pow.mul.base)

    Eq.y = Eq[-2].subs(Eq[-1])

    Eq << Eq.y.find(Mul[Add ** (S.One / 2)]).this.apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Mul[Add ** 2]).apply(algebra.mul.to.pow.mul.base)

    Eq << (-Eq[-1].rhs.find(Mul[Add ** 3])).this.apply(algebra.mul.to.pow.mul.base) * 27

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.mul.base)

    Eq << algebra.eq.imply.eq.div.apply(Eq[-1], 27)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq.y.subs(Eq[-1])

    Eq <<= Eq[-1] - alpha, Eq[-1] + alpha

    Eq << Eq.root.subs(Eq[-1], Eq[-2])

    #https://planetmath.org/QuarticFormula
    #https://en.wikipedia.org/wiki/Quartic_equation


if __name__ == '__main__':
    run()
# created on 2018-11-26
