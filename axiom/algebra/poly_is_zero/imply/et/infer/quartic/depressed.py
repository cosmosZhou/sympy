from util import *


@apply
def apply(fx, x=None):
    from axiom.algebra.poly_is_zero.imply.et.infer.quartic.one_leaded import quartic_coefficient
    from axiom.algebra.poly_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
    from axiom.algebra.ne_zero.poly_is_zero.imply.ne import cubic_delta
    fx = fx.of(Equal[0])
    _1, _0, alpha, beta, gamma = quartic_coefficient(fx, x=x)
    assert _0 == 0 and _1 == 1

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2

    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    from axiom.algebra.poly_is_zero.ne_zero.imply.et.infer.quartic.depressed import solver_set
    delta = alpha ** 2 - 4 * gamma

    return Infer(Equal(beta, 0), Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))), \
        Infer(Unequal(beta, 0) & Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), \
        Infer(Unequal(beta, 0) & Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), \
        Infer(Unequal(beta, 0) & Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from axiom import algebra

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), x=x)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=Equal(beta, 0))

    Eq <<= algebra.infer.imply.infer.subs.apply(Eq[-2]), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(algebra.poly_is_zero.imply.ou_eq.biquadratic, x)

    Eq << algebra.infer.imply.et.infer.apply(Eq[-1].this.rhs.apply(algebra.poly_is_zero.ne_zero.imply.et.infer.quartic.depressed, x), None)

    # Eq << Eq[-3].this.apply(algebra.suffice.flatten)
    # Eq << Eq[-2].this.apply(algebra.suffice.flatten)
    # Eq << Eq[-1].this.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()  # created on 2018-11-27
# updated on 2018-11-27
