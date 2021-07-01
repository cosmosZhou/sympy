from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])
    
    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(All[x:a:b](Greater(f(x), g(x))))
    

if __name__ == '__main__':
    run()

