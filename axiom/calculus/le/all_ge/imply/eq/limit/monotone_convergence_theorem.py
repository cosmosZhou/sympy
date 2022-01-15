from util import *


@apply
def apply(le, any_all_ge):
    an1, an = le.of(LessEqual)
    ((_an, _M), (n, _0, b)), (M,) = any_all_ge.of(Any[All[GreaterEqual]])
    assert an == _an
    assert b == oo
    assert M == _M
    assert an._subs(n, n + 1) == an1
    return Equal(Limit[n:oo](an), Inf[n:0:oo](an))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] <= a[n], Exists[M](ForAll[n:0:oo](a[n] >= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_lt = Exists[N](a[N] < Eq[2].find(Inf) + epsilon, plausible=True)

    Eq << ~Eq.any_lt

    Eq << Eq[-1].this.expr.apply(algebra.all_ge.imply.inf_ge)

    Eq.any_ge = Eq[-1].this.find(Inf).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(algebra.all_ge.imply.inf_ge)

    Eq << Eq[-1].this.expr.apply(algebra.ge.imply.gt.relax, lower=-oo)

    Eq.le_inf = algebra.imply.all_le.inf.apply(Eq[-1].lhs)

    Eq << algebra.le.imply.lt.relax.apply(Eq.le_inf, upper=oo)

    Eq.inf_is_real = sets.gt.lt.imply.el.interval.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq.inf_is_real, Eq.any_ge, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.ge.el.imply.ge.sub)

    Eq << Eq.any_lt.this.expr - epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq << -Eq[-1].this.expr

    Eq.any_gt = Eq[-1].this.expr + a[N]

    Eq << algebra.le.imply.all_le.monotone.apply(Eq[0], n, N)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << algebra.cond.all.imply.all_et.apply(Eq.inf_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.le.el.imply.le.sub)

    Eq << algebra.all.any.imply.any_all_et.apply(Eq[-1], Eq.any_gt)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.le.imply.lt.transit)

    Eq << algebra.le.imply.eq.abs.apply(Eq.le_inf)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.neg)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-24
