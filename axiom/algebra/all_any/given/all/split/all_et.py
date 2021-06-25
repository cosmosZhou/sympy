from util import *


@apply
def apply(given): 
    et, *limits = given.of(All[And])    
    return tuple(All(eq, *limits) for eq in et)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(All[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))
    
    Eq <<= Eq[1] & Eq[2] & Eq[3]

    
if __name__ == '__main__':
    run()

