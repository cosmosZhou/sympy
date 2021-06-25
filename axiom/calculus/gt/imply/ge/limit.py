from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)
    
    return GreaterEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Greater(f(x) / x, g(x) / x), (x, 0))    


if __name__ == '__main__':
    run()

