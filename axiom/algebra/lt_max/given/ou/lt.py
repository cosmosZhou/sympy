from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Expr < Max)
    first = args[:index]
    second = args[index:]

    return Less(x, Max(*first)) | Less(x, Max(*second))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x < Max(y, z))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.apply(algebra.et.imply.ou)

    


if __name__ == '__main__':
    run()
# created on 2022-01-02
