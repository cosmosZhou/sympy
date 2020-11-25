from axiom.utility import plausible
from sympy.core.relational import LessThan, Equal
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.sets.contains import Contains
from axiom import algebre, sets
from sympy.functions.elementary.integers import ceiling
from sympy.concrete.expr_with_limits import ForAll
from sympy.core.function import Function


@plausible
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
        if domain.is_GreaterThan:
            a = domain.rhs
        elif domain.is_StrictGreaterThan:
            a = ceiling(domain.rhs)
        else:
            return
            
    eq = given.function
    assert eq.is_Equality
    lhs, rhs = eq.args
    assert lhs == rhs._subs(n, n + 1)
    assert lhs.is_complex and rhs.is_complex
    return ForAll[n:a:oo](Equal(rhs, rhs._subs(n, a)), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)    
    a = Symbol.a(integer=True)
    f = Function.f(nargs=(), shape=())
    Eq << apply(ForAll[n:a:oo](Equal(f(n + 1), f(n))))   
    
    Eq << Eq[0] - Eq[0].rhs
    
    _n = Symbol.n(domain=Interval(a, oo, integer=True))
    Eq << Eq[-1].sum((n, a, _n))
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << Eq[-1].forall((_n,))
    
    Eq << Eq[-1].limits_subs(n, n - 1)
    
    Eq << Eq[1].bisect({a})


if __name__ == '__main__':
    prove(__file__)
