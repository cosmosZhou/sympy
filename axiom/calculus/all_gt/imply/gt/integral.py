from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Greater])
    
    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](Greater(f(x), g(x))))
    

if __name__ == '__main__':
    run()

