from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Inf >= Expr)
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)) >= y)

    z = Symbol(Eq[0].lhs)
    Eq << z.this.definition

    Eq <<= algebra.eq_inf.imply.all_ge.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed)

    Eq <<= algebra.cond.all.imply.all_et.apply(Eq[-2], Eq[-1], simplify=None)
    Eq <<= Eq[-1].this.expr.apply(algebra.ge.ge.imply.ge.transit)


if __name__ == '__main__':
    run()
# created on 2019-04-06
