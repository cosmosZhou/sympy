from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    x, a, b, c = quadratic_coefficient(fx, x=x)

    delta = b * b - 4 * a * c

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    
    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), 
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), Interval(m, M)) & (a < 0)), 
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x ** 2 + b * x + c, x)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=a > 0)

    Eq <<= Eq[-2].this.lhs.apply(algebra.is_positive.imply.is_nonnegative)

    Eq <<= algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=a > 0)

    Eq <<= Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << algebra.suffice.given.cond.apply(Eq[-1])

    Eq << algebra.cond.imply.suffice.et.apply(Eq[0], cond=Eq[2].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.is_positive.lt.imply.eq.sup.st.quadratic, a * x ** 2 + b * x + c, x)
    Eq << algebra.lt.imply.eq.sup_add.to.expr.doit.st.simple.apply(Eq[0], b * x + c, x)


if __name__ == '__main__':
    run()
