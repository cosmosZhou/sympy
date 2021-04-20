from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom


@apply
def apply(*imply): 
    cond, cond_sum = imply
    fa, ga = axiom.is_Equal(cond)
    
    fx_sum, gx_sum = axiom.is_Equal(cond_sum)
    
    fk, *limits = axiom.is_UNION(fx_sum)
    k, a, b = axiom.limit_is_Interval(limits)    
    assert fk._subs(k, a - 1) == fa
    
    gk, *_limits = axiom.is_UNION(gx_sum)
    assert _limits == limits    
    assert gk._subs(k, a - 1) == ga
    
    return Equal(UNION[k:a - 1:b](fk), UNION[k:a - 1:b](gk))


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Equal(g(a - 1), f(a - 1)), Equal(UNION[k:a:b](g(k)), UNION[k:a:b](f(k))))
    
    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[1])
    
#     Eq << Eq[2].this.lhs.bisect({a - 1})
    
#     Eq << Eq[-1].this.rhs.bisect({a - 1})

    
if __name__ == '__main__':
    prove()

