from util import *


@apply
def apply(given):
    fx, (x, n) = given.of(Derivative < 0)
    assert n == 1
    
    domain = x.domain
    
    assert domain.right_open
    a, b = domain.of(Interval) 
    
    return Greater(fx, fx._subs(x, b))


@prove(proved=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(domain=Interval(a, b, right_open=True))
    
    f = Function.f(real=True)
    
    Eq << apply(Derivative[x](f(x)) < 0)


if __name__ == '__main__':
    run()

