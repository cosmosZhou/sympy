from util import *
import axiom



@apply
def apply(given):
    x_less_than_y, x_less_than_b = given.of(And)
    x, y = x_less_than_y.of(Greater)
    _x, b = x_less_than_b.of(Greater)
    assert x == _x
    return Greater(x, Max(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    b = Symbol.b(real=True, given=True)

    Eq << apply((x > y) & (x > b))

    Eq << algebra.et.given.conds.apply(Eq[0])

    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[1], b)

    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[1], y)

if __name__ == '__main__':
    run()
