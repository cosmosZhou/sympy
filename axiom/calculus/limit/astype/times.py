from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self): 
    expr, (x, x0, dir) = axiom.is_Limit(self)
    args = axiom.is_Times(expr)
    
    coefficient = []
    factors = []
    for arg in args:
        if arg._has(x):
            factors.append(arg)
        else:
            coefficient.append(arg)
    
    coefficient = Times(*coefficient)
    factors = Times(*factors)
    return Equal(self, coefficient * Limit[x:x0:dir](factors).doit())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    
    Eq << apply(Limit[x:x0](f(x) * y))    

    
if __name__ == '__main__':
    prove(__file__)
