from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self): 
    expr, (x, x0, dir) = axiom.is_Limit(self)
    args = axiom.is_Plus(expr)
    
    return Equal(self, Plus(*(Limit[x:x0:dir](arg) for arg in args)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Limit[x:x0](f(x) + g(x)))    

    
if __name__ == '__main__':
    prove(__file__)
