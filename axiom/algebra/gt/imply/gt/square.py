from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    assert lhs.is_real
    assert rhs.is_real
    assert rhs >= 0

    return Greater(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(Greater(x, y))

    Eq << algebra.gt.gt.imply.gt.multiply.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

