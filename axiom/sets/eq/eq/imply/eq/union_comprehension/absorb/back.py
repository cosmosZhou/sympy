from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom


@apply
def apply(*imply): 
    cond, cond_sum = imply
    fb, gb = axiom.is_Equal(cond)
    
    fx_sum, gx_sum = axiom.is_Equal(cond_sum)
    
    fk, *limits = axiom.is_UNION(fx_sum)
    k, a, b = axiom.limit_is_Interval(limits)    
    assert fk._subs(k, b) == fb
    
    gk, *_limits = axiom.is_UNION(gx_sum)
    assert _limits == limits    
    assert gk._subs(k, b) == gb
    
    return Equal(UNION[k:a:b + 1](fk), UNION[k:a:b + 1](gk))


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Equal(g(b), f(b)), Equal(UNION[k:a:b](g(k)), UNION[k:a:b](f(k))))
    
    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[1])

#     Eq << Eq[2].this.lhs.bisect({b})

#     Eq << Eq[-1].this.rhs.bisect({b})

    
if __name__ == '__main__':
    prove()


