from util import *


@apply
def apply(imply):
    equal_positive, equal_negative = imply.of(Or)
    y, x = equal_positive.of(Equal)
    _y, _x = equal_negative.of(Equal)
    if y != _y:
        _y, _x = _x, _y

    assert y == _y
    assert x == -_x

    return Equal(abs(y), abs(x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(Equal(y, x) | Equal(y, -x))

    Eq << Eq[-1] ** 2

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[0] - x


if __name__ == '__main__':
    run()

