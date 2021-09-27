from util import *


@apply
def apply(eq, is_nonzero_real, delta=None):
    A, R = is_nonzero_real.of(Element)
    assert R == Reals - {0}
    fx, (x, x0, dir) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    x, x0 = Symbol(real=True)
    A = Symbol(complex=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), Element(A, Reals - {0}))

    Eq << sets.el.imply.any_eq.apply(Eq[1], var='a')

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, simplify=None, ret=0)

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.is_nonzero)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Eq[-1].this.expr.apply(calculus.is_nonzero.eq.imply.any_all.lt)


if __name__ == '__main__':
    run()
