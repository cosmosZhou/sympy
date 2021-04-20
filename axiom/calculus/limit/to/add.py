from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    expr, (x, x0, dir) = axiom.is_Limit(self)
    args = axiom.is_Add(expr)
    
    return Equal(self, Add(*(Limit[x:x0:dir](arg) for arg in args)))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Limit[x:x0](f(x) + g(x)))
    
    A = Symbol.A(Eq[0].rhs.args[0])    
    B = Symbol.B(Eq[0].rhs.args[1])
    
    Eq << A.this.definition
    
    Eq << B.this.definition

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties