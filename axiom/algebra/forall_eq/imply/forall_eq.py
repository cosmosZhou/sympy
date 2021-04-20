from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(given):
    assert given.is_ForAll
    assert len(given.limits) == 1
    n, *ab = given.limits[0]
    assert n.is_integer
    if len(ab) == 2:
        a, b = ab
        assert b.is_Infinity
        assert a.is_integer and a.is_finite
    elif len(ab) == 1:
        domain = ab[0]
        assert domain.is_Relational
        assert domain.lhs == n
        if domain.is_GreaterEqual:
            a = domain.rhs
        elif domain.is_Greater:
            a = ceiling(domain.rhs)
        else:
            return
            
    eq = given.function
    assert eq.is_Equal
    lhs, rhs = eq.args
    assert lhs == rhs._subs(n, n + 1)
    assert lhs.is_complex and rhs.is_complex
    return ForAll[n:a:oo](Equal(rhs, rhs._subs(n, a)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)    
    a = Symbol.a(integer=True)
    f = Function.f(shape=())
    Eq << apply(ForAll[n:a:oo](Equal(f(n + 1), f(n))))   
    
    Eq << Eq[0].this.function - Eq[0].rhs
    
    _n = Symbol.n(domain=Interval(a, oo, integer=True))
    Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[-1], Interval(a, _n - 1, integer=True))
    
    Eq << algebra.forall_eq.imply.eq.sum.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << Eq[-1].forall((_n,))
    
    Eq << Eq[-1].limits_subs(n, n - 1).reversed
    
    Eq << algebra.forall.given.et.apply(Eq[1], cond={a})


if __name__ == '__main__':
    prove()
