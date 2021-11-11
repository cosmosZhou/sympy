from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    y0 = a * m + b
    y1 = a * M + b

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x + b, x)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=a > 0)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-2], cond=Eq[0]), algebra.cond.given.et.infer.split.apply(Eq[-1], cond=a < 0)

    Eq <<= Eq[-3].this.lhs.apply(algebra.gt_zero.lt.imply.eq.sup.to.max.st.simple, a * x + b, x), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-2], cond=Eq[0]), algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(algebra.lt_zero.lt.imply.eq.sup.to.max.st.simple, a * x + b, x), algebra.infer.given.cond.apply(Eq[-1])

    Eq <<= Eq[-1].this.find(Sup).simplify()

    Eq <<= sets.lt.imply.interval_ne_empty.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-12-25
# updated on 2019-12-25
