from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given): 
    x0, argmin_fx = axiom.is_Equal(given, rhs=ArgMin)
    function, limit = axiom.is_ArgMin(argmin_fx)
    x = limit[0]
    fx0 = function._subs(x, x0)
    return Equal(fx0, MIN(function, limit))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMin[x](f(x))))
    
    
if __name__ == '__main__':
    prove()
