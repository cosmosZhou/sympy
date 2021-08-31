from util import *


@apply
def apply(self):
    x, y = self.of(Arg[Expr + ImaginaryUnit * Expr])
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(x, 0) & Equal(y, 0)),
                                 (asin(y / r), x >= 0),
                                 (S.Pi - asin(y / r), y >= 0),
                                 (-S.Pi - asin(y / r), True)))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x, y = Symbol(real=True)
    Eq << apply(Arg(x + y * S.ImaginaryUnit))

    Eq << Eq[0].this.lhs.apply(geometry.arg.to.piece.acos)

    Eq << Eq[-1].this.find(acos).apply(geometry.acos.to.piece.asin)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.flatten, 1)

    Eq << Eq[-1].this.find(acos).apply(geometry.acos.to.piece.asin)

    Eq << Eq[-1].this.find(-Piecewise).apply(algebra.mul_piece.to.piece)

    Eq.eq = Eq[-1].this.lhs.apply(algebra.piece.invert)

    ou = Eq.eq.find(Or)
    Eq.equivalent = Equivalent(ou & (x / sqrt(x ** 2 + y ** 2) >= 0), (x >= 0) & ou, plausible=True)

    Eq << algebra.equivalent.given.et.suffice.apply(Eq.equivalent)

    Eq <<= Eq[-2].this.find(Or).apply(algebra.ou_is_nonzero.imply.sqrt_is_positive), Eq[-1].this.find(Or).apply(algebra.ou_is_nonzero.imply.sqrt_is_positive)

    Eq <<= Eq[-2].this.lhs.apply(algebra.is_nonnegative.is_positive.imply.is_nonnegative), Eq[-1].this.lhs.apply(algebra.is_positive.ge.imply.ge.div)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq.eq, given=Eq.equivalent)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert.delete)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 1)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 0, 3)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq[-1], given=Eq.equivalent)

    Eq.eq1 = Eq[-1].this.lhs.apply(algebra.piece.invert.delete, 0, 3)

    Eq.suffice = Suffice(y >= 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonnegative.imply.eq.abs)

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq.eq2 = algebra.suffice.imply.eq.piece.apply(Eq.suffice, Eq.eq1.lhs)

    Eq.suffice = Suffice(y < 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), -asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.lhs.apply(algebra.is_negative.imply.eq.abs)

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << algebra.piece.invert.apply(Eq.eq2.rhs, 1, 2)

    Eq << algebra.suffice.imply.eq.piece.apply(Eq.suffice, Eq[-1].rhs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.eq2, Eq[-1])

    Eq << Eq.eq1.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 1, 2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 2, 1)

    Eq << algebra.suffice.imply.eq.piece.apply(Eq.suffice, Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, 2)

    Eq << Eq[-1].this.find(Or).simplify()




if __name__ == '__main__':
    run()