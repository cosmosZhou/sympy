from util import *


@apply
def apply(self, evaluate=False):
    args = []

    for arg in self.of(Mul):
        if arg.is_Abs:
            args.append(arg.of(Abs))
            continue
        elif arg.is_Pow:
            if arg.base.is_Abs and arg.exp.is_integer:
                args.append(Pow(arg.base.of(Abs), arg.exp))
                continue

        assert arg >= 0
        args.append(arg)

    return Equal(self, Abs(Mul(*args), evaluate=evaluate))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(abs(x) * abs(y))

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.args[0].expr.apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.flatten, index=0)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 0)

    Eq << Eq[-1].this.lhs.args[1].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)

    Eq.equal = Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)

    Eq.suffice = Infer(Eq.equal.lhs.args[1].cond, Equal(x * y, 0), plausible=True)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq.suffice)

    Eq <<= Eq[-2].this.lhs.apply(algebra.et.imply.cond, index=1), Eq[-1].this.lhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-2].this.lhs * x

    Eq << Eq[-1].this.lhs * y

    Eq << -Eq.suffice.this.rhs

    Eq << Eq[-1].apply(algebra.infer.imply.iff)

    Eq << algebra.iff.imply.eq.subs.apply(Eq[-1], Eq.equal.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.subs, index=1, reverse=True)

    Eq << Eq.equal.this.lhs.subs(Eq[-1])

    Eq.equal = Eq[-1].this.rhs.apply(algebra.abs.to.piece.gt_zero)

    Eq.equivalent = Equivalent(Eq.equal.lhs.args[0].cond, Eq.equal.rhs.args[0].cond, plausible=True)

    Eq.suffice, Eq.necessary = algebra.iff.given.et.apply(Eq.equivalent)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(algebra.lt_zero.lt_zero.imply.gt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << Eq.necessary.this.rhs.apply(algebra.gt_zero.imply.ou)

    Eq << algebra.iff.imply.eq.subs.apply(Eq.equivalent, Eq.equal.lhs)


if __name__ == '__main__':
    run()

# created on 2018-02-11
# updated on 2018-02-11
