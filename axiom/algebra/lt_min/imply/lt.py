from util import *


@apply
def apply(lt, index=0):
    x, args = lt.of(Less[Expr, Min])
    y = args[index]

    return Less(x, y)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x < Min(y, z))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]
    #Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-01-11
# updated on 2020-01-11
