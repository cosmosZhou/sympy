from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(self):
    function, *limits_d = axiom.is_Derivative(self)
    f, *limits_s = axiom.is_Sum(function)
    
    return Equal(self, Sum(Derivative(f, *limits_d).doit(), *limits_s))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    n = Symbol.n(integer=True)
    Eq << apply(Derivative[x](Sum[n:0:oo](f[n](x))))


if __name__ == '__main__':
    prove()

