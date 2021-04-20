from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, evaluate=False):
    args = []
    
    for arg in axiom.is_Mul(self, copy=True):
        if arg.is_Abs:
            args.append(axiom.is_Abs(arg))
        else:
            assert arg >= 0
            args.append(arg)
    
    return Equal(self, Abs(Mul(*args), evaluate=evaluate))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(abs(x) * abs(y))
    
    Eq << Eq[-1].this.lhs.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.flatten)

#     Eq << Eq[-1].this.lhs.apply(algebra.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.back)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.lhs.args[0].expr.apply(algebra.mul.to.piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.lhs.args[0].cond.apply(algebra.et.to.ou)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.invert, index=0)
    
    Eq << Eq[-1].this.lhs.args[1].cond.apply(algebra.et.to.ou)
    
    Eq << Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)
    
    Eq.equal = Eq[-1].this.lhs.args[1].cond.args[0].apply(algebra.et.to.ou)
    
    Eq.sufficient = Sufficient(Eq.equal.lhs.args[1].cond, Equal(x * y, 0), plausible=True)
    
    Eq << algebra.sufficient.given.sufficient.split.ou.apply(Eq.sufficient)
    
    Eq <<= Eq[-2].this.lhs.apply(algebra.et.imply.cond, index=1), Eq[-1].this.lhs.apply(algebra.et.imply.cond, index=0)
    
    Eq << Eq[-2].this.lhs * x
    
    Eq << Eq[-1].this.lhs * y
    
    Eq << -Eq.sufficient.this.rhs
    
    Eq << Eq[-1].apply(algebra.sufficient.imply.equivalent)
    
    Eq << algebra.equivalent.imply.eq.subs.apply(Eq[-1], Eq.equal.lhs)
    
    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.subs, index=1, reverse=True)
    
    Eq << Eq.equal.this.lhs.subs(Eq[-1])
    
    Eq.equal = Eq[-1].this.rhs.apply(algebra.abs.to.piecewise.is_positive)
    
    Eq.equivalent = Equivalent(Eq.equal.lhs.args[0].cond, Eq.equal.rhs.args[0].cond, plausible=True)
    
    Eq.sufficient, Eq.necessary = algebra.equivalent.given.cond.apply(Eq.equivalent)
    
    Eq << algebra.sufficient.given.sufficient.split.ou.apply(Eq.sufficient)
    
    Eq << Eq[-2].this.lhs.apply(algebra.is_negative.is_negative.imply.is_positive)
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.is_positive.imply.is_positive.mul)
    
    Eq << Eq.necessary.this.rhs.apply(algebra.is_positive.imply.ou)
    
    Eq << algebra.equivalent.imply.eq.subs.apply(Eq.equivalent, Eq.equal.lhs)
    
        
if __name__ == '__main__':
    prove()

