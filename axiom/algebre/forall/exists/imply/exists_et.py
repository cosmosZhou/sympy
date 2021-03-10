from axiom.utility import prove, apply
from sympy import *
from axiom import algebre
import axiom
from sympy.concrete.limits import limits_dict


@apply
def apply(*given):
    forall, exists = given
    fx, *limits_a = axiom.is_ForAll(forall) 
    fy, *limits_b = axiom.is_Exists(exists)
    
    dict_a = limits_dict(limits_a)
    dict_b = limits_dict(limits_b)
    for key, value in dict_a.items():
        assert key in dict_b
        assert value == dict_b[key]
        
    return Exists(fx & fy, *limits_b)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    x = Symbol.x(real=True)
    f = Function.f(integer=True)
    h = Function.h(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[e:g(e) > 0](f(e) > 0), Exists[e:g(e) > 0, x:f(x) > 0](g(x) > 0))
    
    Eq << algebre.exists.given.exists_et.apply(Eq[-1])
    
    Eq << algebre.exists.imply.exists_et.multiple_variables.apply(Eq[1], simplify=False)
    
    Eq << algebre.forall.imply.sufficient.apply(Eq[0])
    
    Eq << algebre.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << Eq[-3].this.function.args[1].apply(algebre.condition.sufficient.imply.condition.transit, Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

