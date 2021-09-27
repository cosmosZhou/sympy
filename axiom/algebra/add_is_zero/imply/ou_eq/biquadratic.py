from util import *


from axiom.algebra.add_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
from axiom.algebra.is_nonzero.add_is_zero.imply.ne import cubic_delta

@apply
def apply(fx, x=None):
    from axiom.algebra.add_is_zero.imply.et.suffice.quartic.one_leaded import quartic_coefficient
    fx = fx.of(Equal[0])
    _1, _0, alpha, beta, gamma = quartic_coefficient(fx, x=x)
    assert _0 == 0 and _1 == 1
    assert beta == 0
    delta = alpha ** 2 - 4 * gamma
    return Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))



@prove
def prove(Eq):
    from axiom import algebra

    x, alpha, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + gamma
    Eq << apply(Equal(fx, 0), x=x)

    y = Symbol(x ** 2)
    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << algebra.add_is_zero.imply.et.suffice.quadratic.apply(Eq[-1], y)

    Eq << Eq[-1].subs(y.this.definition)

    Eq << Eq[-1].this.args[0].apply(algebra.eq_square.imply.ou_is_zero)

    Eq << Eq[-1].this.args[-1].apply(algebra.eq_square.imply.ou_is_zero)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.transposition)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.transposition)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.transposition)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.transposition)


if __name__ == '__main__':
    run()