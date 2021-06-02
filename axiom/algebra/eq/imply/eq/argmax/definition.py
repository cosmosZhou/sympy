from util import *
import axiom



@apply
def apply(given): 
    x0, argmax_fx = given.of(Equal)
    function, limit = argmax_fx.of(ArgMax)
    x = limit[0]
    fx0 = function._subs(x, x0)
    return Equal(fx0, MAX(function, limit))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))
    
    
if __name__ == '__main__':
    run()
