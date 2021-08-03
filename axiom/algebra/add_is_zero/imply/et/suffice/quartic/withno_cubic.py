from util import *


@apply
def apply(is_zero, x=None):
    from axiom.algebra.add_is_zero.imply.et.suffice.quartic.one_leaded import quartic_coefficient
    fx = is_zero.of(Equal[0])
    _1, _0, alpha, beta, gamma = quartic_coefficient(fx, x=x)
    assert _0 == 0 and _1 == 1

    return Suffice(Equal(alpha, 0), Equal(fx, 0))



@prove
def prove(Eq):
    from axiom import algebra

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 4 + alpha * x ** 2 + beta * x + gamma, 0), x=x)

    y = Symbol(complex=True, given=True)
    Eq << ((x ** 2 + y) ** 2).this.apply(algebra.square.to.add)

    Eq << Eq[-1] + Eq[0]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[-1].this.apply(algebra.eq.transposition, lhs=slice(0, 3))

    Eq << Equal(Eq[-1].rhs, 0).this.apply(algebra.add_is_zero.imply.et.suffice.quadratic, x)

    delta = beta ** 2 - (8 * y - 4 * alpha)(y ** 2 - gamma)
    Eq << delta.this.find(Mul).apply(algebra.mul.to.add, deep=True)

    Eq << algebra.suffice.imply.suffice.split.et.apply(Equal(-8 * y ** 3 + 4 * alpha * y ** 2 + 8 * gamma * y + beta ** 2 - 4 * alpha * gamma, 0).this.apply(algebra.add_is_zero.imply.et.suffice.cubic, y))


if __name__ == '__main__':
    run()