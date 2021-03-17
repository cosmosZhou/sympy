from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given): 
    eq_historic, eq_n = given
    lhs, rhs = axiom.is_Equal(eq_historic)
    _lhs, _rhs = axiom.is_Equal(eq_n)
    fx, *limits_x = axiom.is_LAMBDA(lhs)
    gy, *limits_y = axiom.is_LAMBDA(rhs)
    k, a, b = axiom.limit_is_Interval(limits_x)
    _k, _a, _b = axiom.limit_is_Interval(limits_y)
    assert k == _k
    assert a == _a
    assert b == _b
    assert a.is_zero
    n = b
    assert fx._subs(k, n) == _lhs
    assert gy._subs(k, n) == _rhs
    return Equality(LAMBDA[k:n + 1](fx), LAMBDA[k:n + 1](gy))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    f = Function.f(nargs=(), real=True, shape=())
    g = Function.g(nargs=(), real=True, shape=())
    
    Eq << apply(Equality(LAMBDA[k:n](f(k)), LAMBDA[k:n](g(k))), Equality(f(n), g(n)))
    
    Eq << Eq[-1].bisect(Slice[-1:])
    
    Eq << algebre.et.given.cond.apply(Eq[-1], simplify=None)
        
    
if __name__ == '__main__':
    prove(__file__)
