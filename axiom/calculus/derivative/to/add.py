from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(self):
    function, *limits_d = axiom.is_Derivative(self)
    args = axiom.is_Add(function)
    
    return Equal(self, Add(*(Derivative(arg, *limits_d).doit() for arg in args)))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    g = Function.g(real=True)
    Eq << apply(Derivative[x](f(x) + g(x)))


if __name__ == '__main__':
    prove()

