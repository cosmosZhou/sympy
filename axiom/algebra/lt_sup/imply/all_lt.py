from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup < Expr)
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) < y)

    z = Symbol(real=True)
    Eq << algebra.lt_sup.imply.any_all_lt.apply(Eq[0], z)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Eq[-1].this.expr.apply(algebra.cond.all.imply.all_et, simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.imply.lt.transit)


if __name__ == '__main__':
    run()
# created on 2020-01-15
