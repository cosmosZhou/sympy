from util import *
import axiom



@apply
def apply(given):
    y, fx = given.of(Equal)
    if not fx.is_Ceiling:
        y, fx = fx, y
    assert y.is_integer
    x = fx.of(Ceiling)
    return And(x + 1 > y, y >= x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(integer=True)

    Eq << apply(Equal(y, ceiling(x)))

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq <<= -Eq[-2], -Eq[-1]

    Eq << algebra.lt.le.imply.eq.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.floor.to.mul.ceiling)


if __name__ == '__main__':
    run()