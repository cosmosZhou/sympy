from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_StrictGreaterThan(given)
    n, a, b = axiom.limit_is_Interval(limits, integer=True)
    assert a >= 0 and b > a + 1 or a > 0 and b > a
    
    return StrictGreaterThan(Sum(n * lhs, *limits).simplify(), Sum(n * rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(StrictGreaterThan(f(i), g(i)), (i, 0, n + 1))
    
    k = Symbol.k(domain=Interval(1, n, integer=True))
    
    Eq << Eq[0].subs(i, k)
    
    Eq << Eq[-1] * k    
    
    Eq << Eq[-1].apply(algebre.gt.imply.gt.sum, (k,))
    
    Eq << Eq[-1].this.lhs.limits_subs(k, i)
    
    Eq << Eq[-1].this.rhs.limits_subs(k, i)
    

if __name__ == '__main__':
    prove(__file__)

