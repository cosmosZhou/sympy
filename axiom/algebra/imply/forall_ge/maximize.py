from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(function, *limits): 
    return ForAll(GreaterEqual(MAX(function, *limits), function), *limits)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
     
    Eq << apply(f(x), (x, 0, oo))
    
    
if __name__ == '__main__':
    prove()

