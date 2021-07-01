from util import *
from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair



@apply
def apply(given):
    equal_positive, equal_negative = given.of(Or)
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

    Eq << Eq[0].this.args[0].apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.imply.eq.abs)



if __name__ == '__main__':
    run()

