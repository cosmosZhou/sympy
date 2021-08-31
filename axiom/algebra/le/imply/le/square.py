from util import *



@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)

    assert lhs.is_real
    assert rhs.is_real
    assert lhs >= 0

    return LessEqual(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, nonnegative=True)
    y = Symbol(real=True)

    Eq << apply(LessEqual(x, y))

    Eq << algebra.le.le.imply.le.mul.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

