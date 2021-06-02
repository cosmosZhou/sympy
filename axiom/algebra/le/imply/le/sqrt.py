from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual[Basic ** 2, Basic ** 2])

    assert lhs.is_real
    assert rhs.is_real

    return LessEqual(abs(lhs), abs(rhs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(LessEqual(x * x, y * y))

    Eq << Eq[0] - Eq[0].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << algebra.is_nonpositive.imply.ou.split.multiply.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0] - y

    Eq << Eq[-1].this.args[0].args[0] - y

    Eq << Eq[-1].this.args[0].args[0] + y

    Eq << Eq[-1].this.args[0].args[0] + y

    Eq << Eq[-1].this.args[0].apply(algebra.le.ge.imply.le.abs.both)

    Eq << Eq[-1].this.args[0].apply(algebra.le.ge.imply.le.abs.both)


if __name__ == '__main__':
    run()

