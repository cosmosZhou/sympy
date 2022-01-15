from util import *
from axiom.algebra.poly_is_zero.imply.et.infer.cubic import cubic_root


def quartic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 4:
        return None
    a = fx.nth(4)
    b = fx.nth(3)
    c = fx.nth(2)
    d = fx.nth(1)
    e = fx.nth(0)
    return a, b, c, d, e


@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    _a, _b, _c, _d, _e = quartic_coefficient(fx, x=x)
    a, b, c, d = _b / _a, _c / _a, _d / _a, _e / _a

    alpha = b - 3 * a ** 2 / 8
    beta = a ** 3 / 8 + c - a * b / 2
    gamma = a ** 2 * b / 16 + d - 3 * a ** 4 / 256 - a * c / 4

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2
    from axiom.algebra.ne_zero.poly_is_zero.imply.ne import cubic_delta
    from axiom.algebra.poly_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
    y_delta = cubic_delta(x, alpha, beta, gamma)
    D, Y0, Y1, Y2 = cubic_solve(y_delta, x)
    D = Symbol(D)

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    from axiom.algebra.poly_is_zero.ne_zero.imply.et.infer.quartic.depressed import solver_set
    delta = alpha ** 2 - 4 * gamma

    A = Symbol(A)
    B = Symbol(B)
    d, A_, B_, a_ = cubic_root(_b, _c, _d, _e)
    return Infer(Equal(_a, 0) & Equal(_b, 0) & Equal(_c, 0) & Equal(_d, 0), Equal(_e, 0)), \
            Infer(Equal(_a, 0) & Equal(_b, 0) & Equal(_c, 0) & Unequal(_d, 0), Equal(x, -_e / _d)), \
            Infer(Equal(_a, 0) & Equal(_b, 0) & Unequal(_c, 0), Equal(x, (-_d + sqrt(_d ** 2 - 4 * _c * _e)) / (_c * 2)) | Equal(x, (-_d - sqrt(_d ** 2 - 4 * _c * _e)) / (_c * 2))), \
            Infer(Equal(_a, 0) & Unequal(_b, 0) & Equal(d, 0), Or(Equal(x, A_ + B_ - a_ / 3), Equal(x, A_ * w + B_ * ~w - a_ / 3), Equal(x, A_ * ~w + B_ * w - a_ / 3))), \
            Infer(Equal(_a, 0) & Unequal(_b, 0) & Equal(d % 3, 1), Or(Equal(x, A_ * w + B_ - a_ / 3), Equal(x, A_ * ~w + B_ * ~w - a_ / 3), Equal(x, A_ + B_ * w - a_ / 3))), \
            Infer(Equal(_a, 0) & Unequal(_b, 0) & Equal(d % 3, 2), Or(Equal(x, A_ * ~w + B_ - a_ / 3), Equal(x, A_ + B_ * ~w - a_ / 3), Equal(x, A_ * w + B_ * w - a_ / 3))), \
            Infer(Unequal(_a, 0) & Equal(beta, 0), Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2) - a / 4)), \
            Infer(Unequal(_a, 0) & Unequal(beta, 0) & Equal(D, 0), solver_set(0, A, B, x, alpha, beta, w, -a / 4)), \
            Infer(Unequal(_a, 0) & Unequal(beta, 0) & Equal(D % 3, 1), solver_set(1, A, B, x, alpha, beta, w, -a / 4)), \
            Infer(Unequal(_a, 0) & Unequal(beta, 0) & Equal(D % 3, 2), solver_set(2, A, B, x, alpha, beta, w, -a / 4))


@prove(slow=True)
def prove(Eq):
    from axiom import algebra

    x, a, b, c, d, e = Symbol(complex=True, given=True)
    Eq << apply(Equal(a * x ** 4 + b * x ** 3 + c * x ** 2 + d * x + e, 0), x=x)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= algebra.infer.imply.infer.subs.apply(Eq[-2]), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq <<= algebra.infer.imply.et.infer.apply(Eq[-2].this.rhs.apply(algebra.poly_is_zero.imply.et.infer.cubic), None), Eq[-1].this.rhs.apply(algebra.ne_zero.eq.imply.eq.div)

    Eq << algebra.infer.imply.et.infer.apply(Eq[-1].this.rhs.apply(algebra.poly_is_zero.imply.et.infer.quartic.one_leaded).subs(Eq[1].reversed, Eq[2].reversed, Eq[3].reversed), None)


if __name__ == '__main__':
    run()

from . import one_leaded
from . import depressed
# created on 2018-11-29
