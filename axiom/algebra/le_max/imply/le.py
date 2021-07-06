from util import *


@apply
def apply(le, index=0):
    args, x = le.of(Max <= Expr)
    y = args[index]
    
    return LessEqual(y, x)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(Max(y, z) <= x)

    Eq << ~Eq[1]

    #Eq <<= Eq[-1] & Eq[0]
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()