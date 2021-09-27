from util import *


@apply
def apply(self):
    A, B = self.of(Mul)
    A = A.of(Expr ** (S.One / 3))
    B = B.of(Expr ** (S.One / 3))
    C = (A * B) ** (S.One / 3)
    d = Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    return Equal(self, C * Piecewise((1, Equal(A, 0) | Equal(B, 0) | Equal(d, 0)), (w, Arg(A) + Arg(B) > S.Pi), (~w, True)))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(A ** (S.One / 3) * B ** (S.One / 3) )

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[0], cond=Equal(A, 0) | Equal(B, 0))

    Eq << algebra.suffice.given.suffice.subs.bool.apply(Eq[-2])

    Eq << algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << algebra.suffice.given.suffice.subs.bool.apply(Eq[2], invert=True)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=Eq[-1].find(ExprCondPair[~Equal]))

    Eq <<= algebra.suffice.given.suffice.subs.apply(Eq[-2]), algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.lhs.apply(algebra.ceiling_is_nonzero.imply.ou_eq.arg)

    Eq << Eq[-2].this.lhs.apply(algebra.is_nonzero.is_nonzero.eq.imply.eq.cubic_root)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_arg.to.eq_ceiling, simplify=None)

    Eq << algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])

    Eq <<= algebra.suffice.given.suffice.subs.apply(Eq[-2]), algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)
    Eq <<= Eq[-2].this.lhs.apply(algebra.is_nonzero.is_nonzero.eq.imply.eq.cubic_root)
    Eq <<= Eq[-1].this.lhs.apply(algebra.is_nonzero.is_nonzero.eq.imply.eq.cubic_root)


if __name__ == '__main__':
    run()