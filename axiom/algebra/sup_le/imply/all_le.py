from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup <= Expr)
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) <= M)

    Eq << Eq[0].this.lhs.apply(algebra.sup.to.reducedMin)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMin.to.minima)

    Eq << algebra.minima_le.imply.any_le.apply(Eq[-1])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.cond.all.imply.all_et, simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(algebra.le.le.imply.le.transit)





if __name__ == '__main__':
    run()
# created on 2018-12-27
# updated on 2021-09-30