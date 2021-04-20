from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from axiom.calculus.mul.to.derivative import mul_to_derivative


@apply
def apply(self):
    args = axiom.is_Add(self)
    funcs = []
    limits = None
    for arg in args:
        if arg.is_Mul:
            arg = mul_to_derivative(arg)
            
        function, *limits_d = axiom.is_Derivative(arg)
        funcs.append(function)
        if limits is None:
            limits = limits_d
        else:
            assert limits_d == limits
        
    
    return Equal(self, Derivative(Add(*funcs), *limits))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    g = Function.g(real=True)
    Eq << apply(Derivative[x](f(x)) - Derivative[x](g(x)))


if __name__ == '__main__':
    prove()

