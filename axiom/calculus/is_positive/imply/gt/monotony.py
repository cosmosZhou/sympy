from util import *
import axiom



@apply
def apply(given):
    dfx = axiom.is_positive(given)
    
    fx, *limits = dfx.of(Derivative)
    
    assert len(limits) == 1
    limit = limits[0]
    x, n = limit
    assert n == 1
    
    domain = x.domain
    
    assert domain.left_open
    a, b = domain.of(Interval)
    
    return Greater(fx, fx._subs(x, a))


@prove(surmountable=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(domain=Interval(a, b, left_open=True))
    
    f = Function.f(real=True)
    
    Eq << apply(Derivative[x](f(x)) > 0)


if __name__ == '__main__':
    run()

