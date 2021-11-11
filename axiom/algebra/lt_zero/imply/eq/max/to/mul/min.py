from util import *


@apply
def apply(is_negative, self, div=False):
    factor = is_negative.of(Expr < 0)
    args = self.of(Max)

    if div:
        args = [arg * factor for arg in args]
        rhs = Min(*args) / factor
    else:
        args = [arg / factor for arg in args]
        rhs = Min(*args) * factor
        
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r < 0, Max(r * x, r * y))

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.min.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.to.mul)

    Eq.eq = algebra.eq.given.eq.div.apply(Eq[-1], r)

    Eq.equivalent = Equivalent(Eq[-1].find(GreaterEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << algebra.iff.given.et.apply(Eq.equivalent)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-2], cond=Eq[0]), algebra.assuming.given.assuming_et.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(algebra.lt_zero.ge.imply.le.div), Eq[-1].this.rhs.apply(algebra.lt_zero.le.imply.ge.mul)

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    
    


if __name__ == '__main__':
    run()
# created on 2020-01-19
# updated on 2021-10-02