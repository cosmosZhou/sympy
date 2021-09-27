from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Inf > Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval(M0, oo, left_open=True)](All(fx > M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(a, b, left_open=True, right_open=True)](f(x)) > M0, M)

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition

    Eq <<= algebra.eq_inf.imply.all_ge.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed), algebra.any.given.cond.subs.apply(Eq[1], M, (y + M0) / 2)

    Eq <<= algebra.cond.all.imply.all_et.apply(Eq[-2], Eq[-3], simplify=None), algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-2] * 2 - M0

    Eq << Eq[-3].this.expr.apply(algebra.gt.ge.imply.gt.transit, ret=0)

    Eq << Eq[-1].this.expr.apply(algebra.gt.ge.imply.gt.add)

    Eq << Eq[-1].this.expr / 2


if __name__ == '__main__':
    run()