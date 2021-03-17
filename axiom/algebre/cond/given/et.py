from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import sets, algebre

    
@apply(given=None)
def apply(imply, given):
    assert given.plausible is None
    return And(imply, given)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(f(x) < 0, g(x) > 0)
        
    Eq << algebre.et.imply.cond.apply(Eq[1], index=0)
    
        
if __name__ == '__main__':
    prove(__file__)

