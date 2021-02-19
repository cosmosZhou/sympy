from axiom.utility import prove, apply
from sympy import *
from axiom import algebre
import axiom
from sympy.concrete.limits import limits_include, limits_difference


@apply
def apply(*given):
    forall, forall_exists = given
    
    fx, *limits_a = axiom.is_ForAll(forall)
    
    exists, *limits_b = axiom.is_ForAll(forall_exists)
    assert limits_include(limits_a, limits_b)
    
    limits_a = limits_difference(limits_a, limits_b)
    
    assert limits_a
    fy, *limits_c = axiom.is_Exists(exists)
    return ForAll(Exists(ForAll(fx & fy, *limits_a), *limits_c), *limits_b)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    
    x = Symbol.x(shape=(oo,), etype=dtype.integer)
    
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(domain=Interval(0, k, integer=True))
    s = Symbol.s(etype=dtype.integer.set * (k + 1))
    
    Eq << apply(ForAll[i:Interval(0, k, integer=True) // {j}, x[:k + 1]:s](Equal(x[i] & x[j], x[i].etype.emptySet)),
                ForAll[x[:k + 1]:s](Exists[j](Subset({n}, x[j]))))

    Eq << Eq[-1].this.function.function.apply(algebre.forall.given.ou, depth=0)
    
    Eq << algebre.forall.imply.ou.limits_delete.apply(Eq[0], index=0, simplify=None)
    
    Eq <<= Eq[1] & Eq[-1]
    
    Eq << Eq[-1].this.function.function.astype(Or)
    
    et = Eq[-1].function.function.args[0]
    Eq << Sufficient(et, et.args[0], plausible=True)
    
    Eq << Eq[-2].this.function.function.args[0].apply(algebre.condition.sufficient.imply.condition.transit, Eq[-1], split=False)
    


if __name__ == '__main__':
    prove(__file__)

