from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Less)
    assert lhs.is_integer and rhs.is_integer
    return LessEqual(lhs, rhs - 1)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2018-05-23
