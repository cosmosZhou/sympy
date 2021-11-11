from util import *


def cubic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 3:
        return None
    a = fx.nth(3)
    b = fx.nth(2)
    c = fx.nth(1)
    d = fx.nth(0)
    return a, b, c, d

def cubic_root(_a, _b, _c, _d):
    a, b, c = _b / _a, _c / _a, _d / _a
    q = a ** 3 / 27 * 2 + c - a * b / 3
    p = b - a ** 2 / 3
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    arg_p = Ceiling(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    #arg_AB = Ceiling(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))
    d = arg_p - arg_AB
    return d, A, B, a

@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs
    if x is None:
        for x in fx.free_symbols:
            p = fx.as_poly(x)
            if p and p.degree() == 3:
                break
        else:
            return

    _a, _b, _c, _d = cubic_coefficient(fx, x=x)
    d, A, B, a = cubic_root(_a, _b, _c, _d)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    return Infer(Equal(_a, 0) & Equal(_b, 0) & Equal(_c, 0), Equal(_d, 0)),             Infer(Equal(_a, 0) & Equal(_b, 0) & Unequal(_c, 0), Equal(x, -_d / _c)),             Infer(Equal(_a, 0) & Unequal(_b, 0), Equal(x, (-_c + sqrt(_c ** 2 - 4 * _b * _d)) / (_b * 2)) | Equal(x, (-_c - sqrt(_c ** 2 - 4 * _b * _d)) / (_b * 2))),             Infer(Unequal(_a, 0) & Equal(d, 0), Or(Equal(x, A + B - a / 3), Equal(x, A * w + B * ~w - a / 3), Equal(x, A * ~w + B * w - a / 3))),             Infer(Unequal(_a, 0) & Equal(d % 3, 1), Or(Equal(x, A * w + B - a / 3), Equal(x, A * ~w + B * ~w - a / 3), Equal(x, A + B * w - a / 3))),             Infer(Unequal(_a, 0) & Equal(d % 3, 2), Or(Equal(x, A * ~w + B - a / 3), Equal(x, A + B * ~w - a / 3), Equal(x, A * w + B * w - a / 3)))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c, d = Symbol(complex=True, given=True)
    Eq << apply(Equal(a * x ** 3 + b * x ** 2 + c * x + d, 0), x=x)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= algebra.infer.imply.infer.subs.apply(Eq[-2]), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.poly_is_zero.imply.et.infer.quadratic, x=x), Eq[-1].this.rhs.apply(algebra.ne_zero.eq.imply.eq.div)

    Eq <<= algebra.infer.imply.et.infer.apply(Eq[-2], None), algebra.infer.imply.et.infer.apply(Eq[-1].this.rhs.apply(algebra.poly_is_zero.imply.et.infer.cubic.one_leaded, x), None)

    #Eq <<= Eq[-6].this.apply(algebra.suffice.flatten), Eq[-5].this.apply(algebra.suffice.flatten), Eq[-4].this.apply(algebra.suffice.flatten), Eq[-3].this.apply(algebra.suffice.flatten), Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()
from . import one_leaded
from . import depressed
# created on 2018-11-25
# updated on 2018-11-25
