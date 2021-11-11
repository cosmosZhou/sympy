from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual[Expr, Expr])
    assert lhs >= 0
    return LessEqual(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(LessEqual(x * x, y * y))

    Eq << Eq[0] - Eq[0].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << algebra.le_zero.imply.ou.split.mul.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0] - y

    Eq << Eq[-1].this.args[0].args[0] - y

    Eq << Eq[-1].this.args[0].args[0] + y

    Eq << Eq[-1].this.args[0].args[0] + y

    Eq << Eq[-1].this.args[0].apply(algebra.le.ge.imply.le.abs.both)

    Eq << Eq[-1].this.args[0].apply(algebra.le.ge.imply.le.abs.both)


if __name__ == '__main__':
    run()

# created on 2019-05-31
# updated on 2019-05-31
