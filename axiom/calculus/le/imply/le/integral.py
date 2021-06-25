from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)
    
    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(LessEqual(f(x), g(x)), (x, -oo, oo))
    

if __name__ == '__main__':
    run()

