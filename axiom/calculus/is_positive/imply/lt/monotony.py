from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, calculus


@apply
def apply(given):
    dfx = axiom.is_positive(given)
    
    fx, *limits = axiom.is_Derivative(dfx)
    
    assert len(limits) == 1
    limit = limits[0]
    x, n = limit
    assert n == 1
    
    domain = x.domain
    
    assert domain.is_Interval
    assert domain.right_open
    b = domain.stop 
    
    return StrictLessThan(fx, fx._subs(x, b))


@prove(surmountable=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(domain=Interval(a, b, right_open=True))
    
    f = Function.f(real=True)
    
    Eq << apply(Derivative[x](f(x)) > 0)


if __name__ == '__main__':
    prove(__file__)

