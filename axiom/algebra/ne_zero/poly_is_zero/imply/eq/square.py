from util import *


@apply
def apply(is_nonzero, delta_is_zero, fx):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    _a = is_nonzero.of(Unequal[0])
    [x] = fx.free_symbols - delta_is_zero.free_symbols
    delta = delta_is_zero.of(Equal[0])

    x, a, b, c = quadratic_coefficient(fx, x=x)

    assert (b * b - 4 * a * c).expand() == delta.expand()
    assert a == _a

    return Equal(fx, (sqrt(a) * x + b / (2 * sqrt(a))) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(b ** 2 - 4 * a * c, 0), a * x ** 2 + b * x + c)

    Eq << Eq[-1] / a

    Eq <<= Eq[0] & Eq[-1]

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[1].this.apply(algebra.eq.transport)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2018-11-12
