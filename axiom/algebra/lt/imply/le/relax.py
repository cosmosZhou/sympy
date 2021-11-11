from util import *



@apply
def apply(given):
    assert given.is_Less
    lhs, rhs = given.args
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-12-29
# updated on 2018-12-29
