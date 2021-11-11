from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    assert not x.is_set
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << Eq[0].this.lhs.arg.apply(algebra.expr.to.add.complex)

    Eq.square_is_zero = algebra.eq.imply.eq.pow.apply(Eq[-1], exp=2)

    Eq.Im_is_positive = Greater(Im(x) ** 2, 0, plausible=True)

    Eq << GreaterEqual(Re(x) ** 2, 0, plausible=True)

    Eq << algebra.gt_zero.ge_zero.imply.gt_zero.add.apply(Eq.Im_is_positive, Eq[-1])

    Eq << Eq[-1].subs(Eq.square_is_zero)

    Eq << ~Eq.Im_is_positive

    Eq << algebra.le_zero.imply.is_zero.apply(Eq[-1])

    Eq.Im_is_zero = algebra.square_is_zero.imply.is_zero.real.apply(Eq[-1])

    Eq.Re_is_positive = Greater(Re(x) ** 2, 0, plausible=True)

    Eq << GreaterEqual(Im(x) ** 2, 0, plausible=True)

    Eq << algebra.gt_zero.ge_zero.imply.gt_zero.add.apply(Eq.Re_is_positive, Eq[-1])

    Eq << Eq[-1].subs(Eq.square_is_zero)

    Eq << ~Eq.Re_is_positive

    Eq << algebra.le_zero.imply.is_zero.apply(Eq[-1])

    Eq.Re_is_zero = algebra.square_is_zero.imply.is_zero.real.apply(Eq[-1])

    Eq << algebra.expr.to.add.complex.apply(x)

    Eq << Eq[-1].subs(Eq.Im_is_zero, Eq.Re_is_zero)


if __name__ == '__main__':
    run()

from . import real
# created on 2018-03-16
# updated on 2018-03-16
