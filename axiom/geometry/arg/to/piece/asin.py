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

    Eq << algebra.iff.given.et.infer.apply(Eq.equivalent)

    Eq <<= Eq[-2].this.find(Or).apply(algebra.ou_ne_zero.imply.sqrt_gt_zero), Eq[-1].this.find(Or).apply(algebra.ou_ne_zero.imply.sqrt_gt_zero)

    Eq <<= Eq[-2].this.lhs.apply(algebra.ge_zero.gt_zero.imply.ge_zero), Eq[-1].this.lhs.apply(algebra.gt_zero.ge.imply.ge.div)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert.delete)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 1)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 0, 3)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq[-1], old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq.eq1 = Eq[-1].this.lhs.apply(algebra.piece.invert.delete, 0, 3)

    Eq.suffice = Infer(y >= 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.lhs.apply(algebra.ge_zero.imply.eq.abs)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq.eq2 = algebra.infer.imply.eq.piece.apply(Eq.suffice, Eq.eq1.lhs)

    Eq.suffice = Infer(y < 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), -asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.imply.eq.abs)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << algebra.piece.invert.apply(Eq.eq2.rhs, 1, 2)

    Eq << algebra.infer.imply.eq.piece.apply(Eq.suffice, Eq[-1].rhs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.eq2, Eq[-1])

    Eq << Eq.eq1.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 1, 2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 2, 1)

    Eq << algebra.infer.imply.eq.piece.apply(Eq.suffice, Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, 2)

    

    


if __name__ == '__main__':
    run()
# created on 2018-07-24
# updated on 2022-01-08
