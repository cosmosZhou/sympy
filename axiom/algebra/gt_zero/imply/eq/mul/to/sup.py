from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(self * a, Sup(fx * a, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x, a, b, c = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)))

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    y = Symbol(Eq[1].lhs.args[1])
    Eq << y.this.definition

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed).reversed

    Eq <<= algebra.sup_le.imply.all_le.apply(Eq[-3]), algebra.sup_ge.imply.all_any_gt.apply(Eq[-2]), algebra.eq.given.et.squeeze.apply(Eq[-1])

    y_ = Eq[-3].variable
    Eq <<= algebra.all.imply.infer.apply(Eq[-3]), algebra.sup_le.given.all_le.apply(Eq[-2]), algebra.sup_ge.given.all_any_gt.apply(Eq[-1])

    Eq <<= Eq[-3].subs(y_, Eq[2].lhs * y_), Eq[-2].this.expr.apply(algebra.le.given.et.scale.positive, a, div=True), algebra.all.given.infer.apply(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-2])

    Eq << Eq[-3].this.rhs.apply(algebra.cond.any.imply.any_et, Eq[0], simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.gt.imply.gt.mul)

    Eq << Eq[-1].this.lhs.apply(algebra.lt.given.et.scale.positive, a)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-20
