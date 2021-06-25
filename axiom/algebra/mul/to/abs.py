from util import *


@apply
def apply(self, evaluate=False):
    args = []

    for arg in self.of(Mul):
        if arg.is_Abs:
            args.append(arg.of(Abs))
        else:
            assert arg >= 0
            args.append(arg)

    return Equal(self, Abs(Mul(*args), evaluate=evaluate))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(abs(x) * abs(y))

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.abs.to.piecewise)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.abs.to.piecewise)

    Eq << Eq[-1].this.lhs.apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.back)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.args[0].expr.apply(algebra.mul.to.piecewise)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.flatten, index=0)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.invert, index=0)

    Eq << Eq[-1].this.lhs.args[1].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)

    Eq.equal = Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)

    Eq.suffice = Suffice(Eq.equal.lhs.args[1].cond, Equal(x * y, 0), plausible=True)

    Eq << algebra.suffice.given.suffice.split.ou.apply(Eq.suffice)

    Eq <<= Eq[-2].this.lhs.apply(algebra.et.imply.cond, index=1), Eq[-1].this.lhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-2].this.lhs * x

    Eq << Eq[-1].this.lhs * y

    Eq << -Eq.suffice.this.rhs

    Eq << Eq[-1].apply(algebra.suffice.imply.equivalent)

    Eq << algebra.equivalent.imply.eq.subs.apply(Eq[-1], Eq.equal.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.subs, index=1, reverse=True)

    Eq << Eq.equal.this.lhs.subs(Eq[-1])

    Eq.equal = Eq[-1].this.rhs.apply(algebra.abs.to.piecewise.is_positive)

    Eq.equivalent = Equivalent(Eq.equal.lhs.args[0].cond, Eq.equal.rhs.args[0].cond, plausible=True)

    Eq.suffice, Eq.necessary = algebra.equivalent.given.cond.apply(Eq.equivalent)

    Eq << algebra.suffice.given.suffice.split.ou.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(algebra.is_negative.is_negative.imply.is_positive)

    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq << Eq.necessary.this.rhs.apply(algebra.is_positive.imply.ou)

    Eq << algebra.equivalent.imply.eq.subs.apply(Eq.equivalent, Eq.equal.lhs)


if __name__ == '__main__':
    run()

