from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Unequal)
    assert rhs.is_One
    assert lhs.is_Bool

    return Equal(lhs, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(Bool(x > y), 1))

    Eq << Eq[0].this.lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()
