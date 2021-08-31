from util import *


@apply
def apply(is_nonzero, eq, delta=None):
    A = is_nonzero.of(Unequal[0])
    assert A.is_real
    fx, (x, x0, dir) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Unequal(A, 0), Equal(Limit[x:x0](f(x)), A))

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[2], cond=A > 0)

    Eq.gt, Eq.le = algebra.cond.imply.et.suffice.split.apply(Eq[1], cond=A > 0)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq.gt)

    Eq << Eq[-1].this.rhs.apply(calculus.is_positive.eq.imply.any_all.gt)

    Eq << (A > 0).this.apply(algebra.is_positive.imply.eq.abs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.gt.imply.is_positive.transit, ret=0)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].apply(algebra.is_positive.imply.eq.abs)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq << And(A <= 0, Eq[0]).this.apply(algebra.is_nonzero.is_nonpositive.imply.is_negative)

    Eq << Eq[-1].this.apply(algebra.suffice.fold)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq <<= Eq.le & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(calculus.is_negative.eq.imply.any_all.lt)

    Eq << (A <= 0).this.apply(algebra.is_nonpositive.imply.eq.abs)

    Eq << -Eq[-1].this.rhs

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.lt.imply.is_negative.transit, ret=0)

    Eq << Eq[-1].this.rhs.expr.expr.args[1].apply(algebra.is_negative.imply.eq.abs)

    Eq << -Eq[-1].this.rhs.expr.expr.args[1]

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq << -Eq[-1].this.rhs.expr.expr


if __name__ == '__main__':
    run()