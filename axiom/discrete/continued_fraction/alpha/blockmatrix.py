from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(A): 
    assert A.is_alpha
    assert len(A.args) == 1
    block = A.arg
    args = axiom.is_BlockMatrix(block)
    
    return Equal(A, alpha(*args))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    y = Symbol.y(real=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    
    Eq << apply(alpha(BlockMatrix(x[:n], y)))
    
    Eq.initial = Eq[0].subs(n, 1)
    
    Eq << Eq.initial.this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << algebra.eq.imply.eq.subs.apply(Eq[0], x[:n], x[1:n + 1])
    
    Eq << discrete.imply.is_nonzero.alpha.apply(Eq[-1].lhs.arg)
    
    Eq << algebra.is_nonzero.eq.imply.eq.inverse.apply(Eq[-1], Eq[-2])
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=1)

if __name__ == '__main__':
    prove()

