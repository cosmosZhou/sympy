from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
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

    Eq << Eq[-1].this.function.function.apply(algebra.forall.given.ou)
    
    Eq << Eq[-1].this.function.apply(algebra.exists_ou.given.ou.exists, simplify=None)
    
    Eq << Eq[-1].this.find(Exists).apply(algebra.exists.given.cond, simplify=None)
    
    Eq << Eq[-1].this.function.apply(algebra.ou.given.forall)
    
    Eq << Eq[-1].this.function.apply(algebra.exists_et.given.et, index=0)
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    


if __name__ == '__main__':
    prove()

