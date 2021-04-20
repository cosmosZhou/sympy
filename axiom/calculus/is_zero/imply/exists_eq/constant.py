from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets, calculus


@apply
def apply(given):
    dfx = axiom.is_zero(given)
    fx, *limits = axiom.is_Derivative(dfx)
    C = given.generate_free_symbol(real=True, free_symbol='C')
    return Exists[C](ForAll(Equal(fx, C), *((x,) for x,*_ in limits)))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    
    Eq << apply(Equal(Derivative[x](f(x)), 0))

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

