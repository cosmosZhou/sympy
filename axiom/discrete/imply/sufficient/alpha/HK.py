from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.continued_fraction.HK.definition import H, K


@apply
def apply(x, wrt=None):
    n = x.shape[0]
    assert n.is_finite 
    assert n >= 3
    
    if wrt is None:
        i = x.generate_free_symbol(integer=True, free_symbol='i')
    else:
        i = wrt
    
    return Sufficient(ForAll[i:1:n](x[i] > 0), Equal(alpha(x), H(x) / K(x)))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=False)
    
    Eq << apply(x[:n + 1])
    
    Eq.initial = Eq[0].subs(n, 2)
    
    Eq << Eq.initial.this.lhs.doit()
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.is_positive.imply.is_positive.mul)
    
    Eq << Eq[-1].this.lhs + 1
    
    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.is_nonzero)
    
    Eq << algebra.sufficient.given.sufficient.et.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.multiply.is_nonzero.eq)
    
    Eq << Eq[-1].this.rhs.lhs.ratsimp()
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq.alpha_recurrence = discrete.imply.sufficient.alpha.recurrence.apply(Eq.induct.find(alpha))
    
    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n + 1], BlockMatrix(x[:n], x[n] + 1 / x[n + 1]))
    
    Eq << Eq[-1].this.rhs.lhs.apply(discrete.continued_fraction.alpha.blockmatrix)
    
    Eq << Eq[-1].this.lhs.apply(algebra.forall.given.et, cond={n})
    
    Eq << Eq[-1].this.find(ForAll)().function.simplify()
    
    Eq << Eq[-1].this.find(Greater).apply(algebra.is_positive.given.is_positive.split.add)
    
    Eq << Eq[-1].this.find(Greater).apply(algebra.is_positive.given.is_positive.inverse)
    
    Eq << Eq[-1].this.lhs.apply(algebra.et.to.forall)    
    
    Eq <<= Eq.alpha_recurrence & Eq[-1]
    
    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit)
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.rhs.rhs.ratsimp()

    Eq << Eq.induct.this.find(H).definition
    
    Eq << Eq[-1].this.find(Indexed * ~H).definition
    
    Eq << Eq[-1].this.find(Mul, Add).expand()
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.find(Indexed * ~K).definition
    
    Eq << Eq[-1].this.find(Pow, Add).expand()
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=2)
    

if __name__ == '__main__':
    prove()

