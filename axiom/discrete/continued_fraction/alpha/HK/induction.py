from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import H, K
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(x, n):
    assert n >= 2
    return Equal(alpha(x[:n + 1]), H(x[:n + 1]) / K(x[:n + 1]))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=False)
    
    Eq << apply(x, n)    
    
    Eq.initial = Eq[-1].subs(n, 2)

    Eq <<= alpha(x[:3]).this.definition, H(x[:3]).this.definition, K(x[:3]).this.definition
    
    Eq <<= Eq[-3].this.rhs.subs(alpha(x[1:3]).this.definition), Eq[-2].this.rhs.subs(H(x[:2]).this.definition), Eq[-1].this.rhs.subs(K(x[:2]).this.definition)
    
    Eq <<= Eq[-3].this.rhs.subs(alpha(x[2]).this.definition), Eq[-2].this.rhs.subs(H(x[0]).this.definition), Eq[-1].this.rhs.subs(K(x[0]).this.definition)
    
    Eq << Eq.initial.subs(Eq[-3], Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.pow.to.mul.cancel, x[2])
    
    Eq << Eq[-1] * (x[1] * x[2] + 1)

    Eq << Eq[-1].this.lhs.ratsimp()    

    Eq << Eq[-1].this.rhs.expand()
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.lhs.apply(discrete.continued_fraction.alpha.recurrence)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[1].base.definition

    Eq << H(x[:n + 1]).this.definition
    
    Eq << K(x[:n + 1]).this.definition
    
    Eq << Eq[-3].this.rhs.subs(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.rhs.args[0].expand()
    
    Eq << Eq[-1].this.rhs.args[0].base.expand()
    
    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n + 1], BlockMatrix(x[:n], x[n] + 1 / x[n + 1]))
    
    Eq << Eq[-1].this.lhs.apply(discrete.continued_fraction.alpha.blockmatrix)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[1].base.definition
    
    Eq << Eq[-1].this.rhs.apply(algebra.mul.cancel, x[n + 1])
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=2)
    

if __name__ == '__main__':
    prove()

