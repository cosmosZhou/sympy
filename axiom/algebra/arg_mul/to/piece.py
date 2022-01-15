from util import *


@apply
def apply(self):
    args = self.of(Arg[Mul])
    s = Add(*(Arg(arg) for arg in args))
    return Equal(self, Piecewise((0, Or(*(Equal(arg, 0) for arg in args))), (s - Ceiling(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi, True)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Arg(x * y))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Eq[0].find(Or))

    Eq << algebra.infer.given.infer.subs.bool.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.ou.imply.is_zero)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << algebra.infer.given.infer.subs.bool.apply(Eq[2], invert=True)

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.ne_zero.imply.eq.arg.to.add)


if __name__ == '__main__':
    run()

# created on 2018-10-26
