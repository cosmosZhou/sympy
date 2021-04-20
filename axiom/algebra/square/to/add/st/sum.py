from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    sgm = axiom.is_Square(self)
    xi, *limits = axiom.is_Sum(sgm)
    try:
        i, z, n = axiom.limit_is_Interval(limits)        
    except:
        i = axiom.limit_is_symbol(limits)
        domain = xi.domain_defined(i)
        z, n = axiom.is_Interval(domain)
    assert z == 0
        
    j = self.generate_free_symbol({i}, integer=True, free_symbol='j')
    xj = xi._subs(i, j)
    return Equal(self, 2 * Sum[j:i, i:n](xi * xj) + Sum[i:n](xi ** 2))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)

    x = Symbol.x(real=True, shape=(oo,))

    Eq << apply(Sum[i:n](x[i]) ** 2)
    
    Eq.initial = Eq[0].subs(n, 1)   
    
    Eq << Eq.initial.this.find(Sum).apply(algebra.sum.to.add.doit.outer)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.find(Sum).bisect({n})
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.find(Sum).bisect({n})
    
    Eq << Eq[-1].this.rhs.find(Number * ~Sum).bisect({n})
    
    Eq << Eq[-1].this.rhs.find(Number * ~Sum).apply(algebra.sum.to.add.doit.outer.setlimit)
    
    Eq << Eq[-1].this.rhs.find(Number * ~Sum).simplify()
    
    j = Eq[0].find(Number * ~Sum).variable
    Eq << Eq[-1].this.rhs.find(Indexed * ~Sum).limits_subs(j, i)
    
    Eq << Eq[0].induct(imply=True, reverse=True)
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()
