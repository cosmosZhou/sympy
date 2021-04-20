from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)
    x_sub_x_means = axiom.is_Square(function)
    
    try:
        i, z, n = axiom.limit_is_Interval(limits)
    except: 
        i = axiom.limit_is_symbol(limits)
        domain = function.domain_defined(i)
        z, n = axiom.is_Interval(domain)
        
    assert z == 0
    xi, x_means = axiom.is_Substract(x_sub_x_means)
    
    x, _i = axiom.is_Indexed(xi)
    assert _i == i
    
    x_sum = x_means * n
    
    xi, *limits = axiom.is_Sum(x_sum)
    
    try:
        j, z, _n = axiom.limit_is_Interval(limits)        
    except:
        j = axiom.limit_is_symbol(limits)
        domain = xi.domain_defined(j)
        z, _n = axiom.is_Interval(domain)
        
    assert z == 0
    assert n == _n
    _x, _j = axiom.is_Indexed(xi)
    assert _j == j
    
    assert x == _x 
    
    if j == i:
        j = self.generate_free_symbol(excludes={i}, integer=True, free_symbol='j')
        
    return Equal(self, Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True, shape=(oo,))
    
    Eq << apply(Sum[i:n]((x[i] - Sum[j:n](x[j]) / n) ** 2))
    
    Eq << Eq[-1].this.lhs.function.expand()
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)
    
    Eq << Eq[-1].this.find(Pow, Sum).limits_subs(j, i)
    
    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)
    
    Eq << Eq[-1].this.lhs.find(Mul).args[2].apply(algebra.square.to.add.st.sum)
    
    Eq << Eq[-1].this.lhs.find(Mul).apply(algebra.mul.to.add)    
    
    Eq << Eq[-1].this.rhs.find(Sum, Pow).apply(algebra.square.to.add)
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)
    
    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)
    
    Eq << Eq[-1] * n
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[2].apply(algebra.sum.to.mul)
    
    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.swap.intlimit)
    
    Eq << Eq[-1].this.rhs.args[1].doit()
    
    Eq << Eq[-1].this.rhs.args[1].limits_subs(j, i)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_front)
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)
    
    Eq << Eq[-1].this.rhs.function.expand()
    
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)
    

if __name__ == '__main__':
    prove()

