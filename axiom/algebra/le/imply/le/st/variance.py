from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
from axiom.algebra.square.to.mul.st.sum import dissect_variance


@apply
def apply(given):
    dx, dy = axiom.is_LessEqual(given)
    
    ym, x, i, n = dissect_variance(dx)
        
    dy = axiom.is_Square(dy)    
    
    _ym, y_mean = axiom.is_Substract(dy)
    assert _ym == ym
    y_sum, m1 = axiom.is_Divide(y_mean)
    m = m1 - 1
    yj, (j, *ab) = axiom.is_Sum(y_sum)
    if ab:
        zero, _m = ab
        assert zero == 0
        assert _m == m1
    
    y = LAMBDA[j](yj).simplify()
    
    assert y[m] == ym
    
    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2) + (ym - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2 + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2),
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m + 1]((y[j] - Sum[j:m + 1](y[j]) / (m + 1)) ** 2))


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo,))
    
    m = Symbol.m(domain=Interval(2, oo, integer=True))
    y = Symbol.y(real=True, shape=(m,))
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    Eq << apply((y[m - 1] - Sum[i](x[i]) / n) ** 2 <= (y[m - 1] - Sum[j](y[j]) / m) ** 2)
    
    Eq << Eq[-1].rhs.args[0].this.apply(algebra.sum.to.mul.st.variance)
    
    Eq << Eq[-1].subs(n, n + 1)
    
    Eq << Eq[-1].this.rhs.find(Sum).bisect({n})
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.doit.outer.setlimit)
    
    Eq << Eq[-1].this.lhs.bisect({n})
    
    Eq << Eq[-1].find(Sum, Sum).this.bisect({n})
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].subs(x[n], y[m - 1])
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.mul.st.variance)
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.st.variance)
    
    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.to.mul.st.variance)
    
    Eq << algebra.le.imply.le.st.square.apply(Eq[0])
    
    Eq << Eq[-1].this.lhs.find(Sum).limits_subs(i, j)
    
    Eq << Eq[-1].this.lhs.args[1].find(Sum).limits_subs(i, j)
    
    Eq << Eq[-1].this.lhs.args[1].find(Sum).function.apply(algebra.square.negate)
    
    Eq << Eq[-1].this.rhs.args[0].find(Sum).limits_subs(i, j)

    
if __name__ == '__main__':
    prove()


