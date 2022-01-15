from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Expr >= Min)
    first = args[:index]
    second = args[index:]

    return GreaterEqual(x, Min(*first)) | GreaterEqual(x, Min(*second))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Min(y, z))

    Eq << algebra.le_min.imply.ou.le.apply(Eq[0].reversed)

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].this.args[1].reversed


if __name__ == '__main__':
    run()
# created on 2022-01-02
