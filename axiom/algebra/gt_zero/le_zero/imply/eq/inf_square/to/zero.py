from util import *


@apply
def apply(is_positive, is_nonpositive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    m = is_nonpositive.of(Expr <= 0)
    if x is None:
        x = m.generate_var(M.free_symbols, real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, m <= 0, x=x)

    Eq << algebra.cond.imply.infer.et.apply(Eq[0], cond=m < 0)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.lt_zero.imply.eq.inf_square.to.zero)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[2], cond=m < 0)

    Eq << algebra.cond.imply.infer.et.apply(Eq[0] & Eq[1], cond=m >= 0)

    Eq << Eq[-1].this.rhs.args[1:].apply(algebra.le.ge.imply.eq)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.imply.eq.inf_square.to.zero)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs.lhs, swap=True, reverse=True)




if __name__ == '__main__':
    run()
# created on 2019-08-25
# updated on 2019-08-25
