from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)
    
    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)    
    return Equal(self, Piecewise((0, (m <= 0) & (M >= 0)), (Min(m ** 2, M ** 2), True)))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq << algebra.cond.imply.suffice.et.apply(Eq[0], cond=M <= 0)

    Eq <<= Eq[-1].this.rhs.apply(algebra.is_nonpositive.lt.imply.eq.inf_square.to.square), Eq[-1].this.rhs.apply(algebra.is_nonpositive.lt.imply.eq.min)

    Eq <<= Eq[-1] & Eq[-2]
    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[1], cond=M >= 0)

    Eq <<= algebra.suffice.given.suffice.subs.bool.apply(Eq[-2]), algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-1].this.lhs.apply(algebra.is_negative.imply.is_nonpositive), algebra.cond.given.et.suffice.split.apply(Eq[-2], cond=m <= 0)

    Eq <<= algebra.suffice.given.suffice.subs.bool.apply(Eq[-2]), algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()