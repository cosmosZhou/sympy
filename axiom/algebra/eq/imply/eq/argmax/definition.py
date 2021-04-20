from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given): 
    x0, argmax_fx = axiom.is_Equal(given)
    function, limit = axiom.is_ArgMax(argmax_fx)
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
    prove()
