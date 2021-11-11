from util import *


@apply
def apply(is_positive, self):
    factor = is_positive.of(Expr > 0)
    args = self.of(Min)

    args = [arg * factor for arg in args]
    return Equal(Min(*args), self * factor)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, Min(x, y))

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.min.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.to.mul)

    Eq.eq = algebra.eq.given.eq.div.apply(Eq[-1], r)

    Eq.equivalent = Equivalent(Eq[-1].find(LessEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << algebra.iff.given.et.apply(Eq.equivalent)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-2], cond=Eq[0]), algebra.assuming.given.assuming_et.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt_zero.le.imply.le.div), Eq[-1].this.rhs.apply(algebra.gt_zero.le.imply.le.mul)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)


if __name__ == '__main__':
    run()
# created on 2019-08-16
# updated on 2019-08-16
