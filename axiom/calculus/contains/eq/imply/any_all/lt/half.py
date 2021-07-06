from util import *


@apply
def apply(is_nonzero_real, eq, delta=None):
    A, R = is_nonzero_real.of(Contains)
    assert R == Reals - {0}
    fx, (x, x0, dir) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    x = Symbol.x(real=True)
    A = Symbol.A(complex=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Contains(A, Reals - {0}), Equal(Limit[x:x0](f(x)), A))

    Eq << sets.contains.imply.any_eq.apply(Eq[0], var='a')

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.cond.cond.imply.et, algebra.eq.cond.imply.cond.subs, simplify=None)

    Eq << algebra.any.imply.any_et.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.is_nonzero)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Eq[-1].this.function.apply(calculus.is_nonzero.eq.imply.any_all.lt)


if __name__ == '__main__':
    run()