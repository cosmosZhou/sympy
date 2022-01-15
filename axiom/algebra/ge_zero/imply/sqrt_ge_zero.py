from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x >= 0)

    y = Symbol(nonnegative=True)
    Eq << GreaterEqual(sqrt(y), 0, plausible=True)

    Eq << Eq[-1].subs(y, x)

    Eq << Eq[-1].this.args[0].simplify()
    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-04
