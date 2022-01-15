from util import *


@apply
def apply(self):
    fx, (x, a, b) = self.of(Integral)

    return Equal(self, Piecewise((-Integral[x:Interval(b, a)](fx), a > b), (Integral[x:Interval(a, b)](fx), True)))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(calculus.integral.to.piece.st.interval)

    Eq << Eq[-1].this.rhs.args[1].expr.apply(calculus.integral.to.piece.st.interval)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this.rhs.args[1].cond.reversed

    Eq << Eq[-1].this.rhs.args[0].expr.apply(calculus.neg.to.integral)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, -2)

    Eq << algebra.eq_piece.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.eq)


if __name__ == '__main__':
    run()


from . import st
# created on 2020-05-24
