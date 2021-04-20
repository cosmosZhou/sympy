from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets

def dissect_variance(variance):
    dx = axiom.is_Square(variance)    
    ym, x_mean = axiom.is_Substract(dx)
    
    x_sum, n = axiom.is_Divide(x_mean)
    xi, (i, *ab) = axiom.is_Sum(x_sum)
    x = LAMBDA[i](xi).simplify()
    if ab:
        zero, _n = ab
        assert zero == 0
        assert _n == n
    
    return ym, x, i, n
    
@apply
def apply(self):
    ym, x, i, n = dissect_variance(self)
    return Equal(self, Sum[i:n](ym - x[i]) ** 2 / n ** 2)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    
    m = Symbol.m(integer=True, positive=True)
    y = Symbol.y(real=True, shape=(m,))
    
    i = Symbol.i(integer=True)
    
    Eq << apply((y[m - 1] - Sum[i](x[i]) / n) ** 2)
    
    x_ = Symbol.x(LAMBDA[i](y[m - 1] - x[i]))
    
    Eq << x_[i].this.definition
    
    Eq << Eq[-1] - y[m - 1]
    
    Eq << -Eq[-1]
    
    Eq << Eq[0].lhs.this.subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)
    
#     Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul)
    
    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.add)
    
    Eq << Eq[-1].subs(x_[i].this.definition)
    
    Eq << Eq[0].this.rhs.find(Sum).apply(algebra.sum.limits.domain_defined.delete)

    
if __name__ == '__main__':
    prove()

