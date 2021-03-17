from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    limits = [x for x, *_ in limits]
    
    return Equality(Derivative(lhs, *limits), Derivative(rhs, *limits))


@prove
def prove(Eq): 
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(x), g(x)), (x,))
    
    Eq << Eq[1].subs(Eq[0])

    
if __name__ == '__main__':
    prove(__file__)

