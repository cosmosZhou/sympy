from util import *


@apply
def apply(sub):
    y, x = sub.of(Expr - Expr)

    if y == ceiling(x):
        return Equal(sub, frac(-x))
    if x == floor(y):
        return Equal(sub, frac(y))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    Eq << apply(ceiling(x) - x)

    Eq << Eq[-1].this.rhs.apply(algebra.frac.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)


if __name__ == '__main__':
    run()
