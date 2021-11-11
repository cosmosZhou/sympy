from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    
    assert lhs.is_integer and rhs.is_integer
    return GreaterEqual(lhs - 1, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[0]) - 1


if __name__ == '__main__':
    run()
# created on 2019-07-23
# updated on 2019-07-23
