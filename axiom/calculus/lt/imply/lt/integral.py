from util import *
import axiom



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)
    
    return Less(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Less(f(x), g(x)), (x, -oo, oo))
    

if __name__ == '__main__':
    run()

