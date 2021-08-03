from util import *


@apply
def apply(given):
    dx, dy = given.of(Less[Expr ** 2, Expr ** 2])

    y2, x01_mean = dx.of(Expr - Expr)
    _y2, y01_mean = dy.of(Expr - Expr)

    y01_mean *= 3
    y0, y1 = y01_mean.of(Add)
    _y2 = _y2 * 3 / 2
    assert _y2 == y2

    x01_mean *= 2
    x0, x1 = x01_mean.of(Add)

    return Less(((x0 - x1) ** 2 + (x1 - y2) ** 2 + (y2 - x0) ** 2) / 3 + (y0 - y1) ** 2 / 2,
                (x0 - x1) ** 2 / 2 + ((y0 - y1) ** 2 + (y1 - y2) ** 2 + (y2 - y0) ** 2) / 3)


@prove
def prove(Eq):
    from axiom import algebra
    x0, x1, y0, y1, y2 = Symbol(real=True)
    Eq << apply((y2 - (x0 + x1) / 2) ** 2 < (y2 - (y0 + y1 + y2) / 3) ** 2)

    Eq << Eq[0] * 9

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.square)

    Eq.lt = Eq[-1].this.rhs.apply(algebra.mul.to.square)

    x1_ = Symbol.x1(y2 - x1)
    x0_ = Symbol.x0(y2 - x0)

    Eq.x0_defintion = x0_.this.definition + x0 - x0_

    Eq.x1_defintion = x1_.this.definition + x1 - x1_

    Eq << Eq.lt.lhs.this.subs(Eq.x0_defintion, Eq.x1_defintion)

    Eq << Eq[-1].this.rhs.apply(algebra.square.to.add)

    Eq << Eq[-1].subs(x0_.this.definition, x1_.this.definition)

    Eq.lt = Eq.lt.subs(Eq[-1])

    y1_ = Symbol.y1(y2 - y1)
    y0_ = Symbol.y0(y2 - y0)

    Eq << y0_.this.definition + y0 - y0_

    Eq << y1_.this.definition + y1 - y1_

    Eq << Eq.lt.rhs.this.subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.square.to.add)

    Eq << Eq[-1].subs(y0_.this.definition, y1_.this.definition)

    Eq << Eq.lt.subs(Eq[-1])

    Eq << algebra.mul.to.add.square.apply(Eq[-1].rhs.find(Mul) / 2)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1] + (y0 - y1) ** 2

    Eq.lt = Eq[-1] / 2

    Eq << Eq[1] * 3

    Eq << Eq[-1] - Eq[-1].rhs.args[0] - (y0 - y1) ** 2

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.square.negate)

    Eq.le = LessEqual(Eq[-1].lhs, Eq.lt.lhs, plausible=True)

    Eq << Eq.le.this.apply(algebra.le.simplify.terms.common)

    Eq << Eq[-1].subs(Eq.x0_defintion, Eq.x1_defintion)

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.le.given.is_nonnegative.apply(Eq[-1])

    Eq << Eq[-1] / 5 * 8

    Eq << algebra.imply.is_nonnegative.square.apply(x0_ + x1_)

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq.lt, Eq.le)


if __name__ == '__main__':
    run()

