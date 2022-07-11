from util import *


@apply
def apply(given, M=None):
    lim, a = given.of(Equal)
    expr, (n, *_) = lim.args
    assert n.is_integer
    if M is None:
        M = Symbol(positive=True)
    else:
        assert M.domain == Interval(0, oo, left_open=True)
    return Any[M](All[n](abs(expr) <= M))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    n = Symbol(integer=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    a = Symbol(real=True, given=True)
    Eq << apply(Equal(Limit[n:oo](x[n]), a))

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0])

    ε = Eq[-1].expr.expr.rhs
    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.imply.lt.abs.max)

    Eq.lt = Eq[-1].subs(ε, S.Half)

    N = Eq.lt.variable
    a_max = Eq.lt.expr.expr.rhs
    M = Symbol(Max(a_max, Maxima[n:N + 1](abs(x[n]))))
    Eq << M.this.definition

    Eq << LessEqual(a_max, M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq.lt.this.expr.expr.apply(algebra.lt.le.imply.lt.transit, Eq[-1])

    Eq.less_than = Eq[-1].this.expr.expr.apply(algebra.lt.imply.le.relax)

    Eq << algebra.imply.all_ge.maxima.apply(Maxima[n:N + 1](abs(x[n])))

    Eq << LessEqual(Maxima[n:N + 1](abs(x[n])), M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-2].this.expr.apply(algebra.ge.le.imply.le.transit, Eq[-1])

    Eq << algebra.any_all.all.imply.any_all.apply(Eq.less_than, Eq[-1])

    Eq.any = Eq[-1].this.expr.simplify()

    Eq << algebra.any.given.any.subs.apply(Eq[1], Eq[1].variable, M)

    Eq << Eq[-1].this.find(Element).apply(sets.el.given.gt_zero)

    Eq.is_nonzero = Unequal(M, 0, plausible=True)

    Eq << Eq.is_nonzero.this.lhs.definition

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.eq_max.imply.et.ge, index=1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.le_zero.imply.is_zero, simplify=None)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.eq_max.imply.et.ge, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.delete, index=0)

    Eq << Eq[-1].this.args[0].apply(algebra.abs_le_zero.imply.is_zero)

    Eq << Eq[-1].this.args[0].apply(algebra.abs_le_zero.imply.is_zero)





    Eq << Eq[-1].this.apply(algebra.eq.eq.imply.eq.sub)

    Eq << GreaterEqual(M, 0, plausible=True)

    Eq << algebra.ne_zero.ge_zero.imply.gt_zero.apply(Eq.is_nonzero, Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.any)


if __name__ == '__main__':
    run()

# created on 2020-05-16
