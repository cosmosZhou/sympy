from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_dict


@apply
def apply(*given):
    forall, exists = given
    if forall.is_Exists:
        forall, exists = exists, forall
        
    fx, *limits_f = axiom.is_ForAll(forall) 
    fy, *limits_e = axiom.is_Exists(exists)
    
    dict_f = limits_dict(limits_f)
    dict_e = limits_dict(limits_e)
    for key, domain_f in dict_f.items():
        assert key in dict_e
        
        domain_e = dict_e[key]
        
        if domain_f == []:
            domain_f = key.universalSet
        elif domain_f.is_boolean:
            domain_f = conditionset(key, domain_f)
            
        if domain_e == []:
            domain_e = key.universalSet
        elif domain_e.is_boolean:
            domain_e = conditionset(key, domain_e)
            
        assert domain_f.is_set
        assert domain_e.is_set
        
        assert domain_e in domain_f
        
    return Exists(fx & fy, *limits_e)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[y:g(y) > 0](f(y) > 0), Exists[y:g(y) > 1, x:f(x) > 0](g(x) > 0))
    
    Eq << algebra.exists.given.exists_et.apply(Eq[-1])
    
    Eq.exists = algebra.exists.imply.exists_et.multiple_variables.apply(Eq[1], simplify=False)
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[0])
    
    Eq << Eq[-1].this.lhs.apply(algebra.gt.given.gt.astrict, 1)
    
    Eq << algebra.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << Eq.exists.this.function.args[2].apply(algebra.cond.sufficient.imply.cond.transit, Eq[-1])
    

if __name__ == '__main__':
    prove()

