from util import *


@apply
def apply(lt, index=0):
    x, args = lt.of(LessEqual[Expr, Min])
    y = args[index]
    
    return LessEqual(x, y)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(x <= Min(y, z))

    Eq << ~Eq[1]

    #Eq <<= Eq[-1] & Eq[0]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()