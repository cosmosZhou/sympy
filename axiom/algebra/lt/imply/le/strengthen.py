from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Less)
    assert lhs.is_integer and rhs.is_integer
    return LessEqual(lhs, rhs - 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
