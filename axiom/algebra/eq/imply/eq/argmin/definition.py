from util import *


@apply
def apply(given): 
    (function, (x,)), x0 = given.of(Equal[ArgMin])    
    fx0 = function._subs(x, x0)
    return Equal(fx0, Minimize[x](function))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMin[x](f(x))))

    
if __name__ == '__main__':
    run()
