from util import *


@apply
def apply(ge, any_all_le):
    an1, an = ge.of(GreaterEqual)
    ((_an, _M), (n, _0, b)), (M,) = any_all_le.of(Any[All[LessEqual]])
    assert an == _an
    assert b == oo
    assert M == _M
    assert an._subs(n, n + 1) == an1
    return Equal(Limit[n:oo](an), Sup[n:0:oo](an))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] >= a[n], Exists[M](ForAll[n:0:oo](a[n] <= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_gt = Exists[N](a[N] > Eq[2].find(Sup) - epsilon, plausible=True)

    Eq << ~Eq.any_gt

    Eq << Eq[-1].this.expr.apply(algebra.all_le.imply.sup_le)

    Eq.any_le = Eq[-1].this.find(Sup).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(algebra.all_le.imply.sup_le)

    Eq << Eq[-1].this.expr.apply(algebra.le.imply.lt.relax, upper=oo)

    Eq.ge_sup = algebra.imply.all_ge.sup.apply(Eq[-1].lhs)

    Eq << algebra.ge.imply.gt.relax.apply(Eq.ge_sup, lower=-oo)

    Eq.sup_is_real = sets.lt.gt.imply.el.interval.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq.sup_is_real, Eq.any_le, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.le.el.imply.le.sub)

    Eq << Eq.any_gt.this.expr + epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq.any_lt = Eq[-1].this.expr - a[N]

    Eq << algebra.ge.imply.all_ge.monotone.apply(Eq[0], n, N)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << -Eq[-1].this.expr

    Eq << algebra.cond.all.imply.all_et.apply(Eq.sup_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.le.el.imply.le.add)

    Eq << algebra.all.any.imply.any_all_et.apply(Eq[-1], Eq.any_lt)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.le.imply.lt.transit)

    Eq << algebra.ge.imply.eq.abs.apply(Eq.ge_sup)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.neg)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-20
