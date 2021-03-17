from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(self):
    function, *limits_d = axiom.is_Derivative(self)
    args = axiom.is_Plus(function)
    
    return Equality(self, Plus(*(Derivative(arg, *limits_d).doit() for arg in args)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    g = Function.g(real=True)
    Eq << apply(Derivative[x](f(x) + g(x)))


if __name__ == '__main__':
    prove(__file__)

