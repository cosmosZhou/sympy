from util import *
import axiom


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)
    
    return LessEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Less(f(x) / x, g(x) / x), (x, 0))    


if __name__ == '__main__':
    run()

