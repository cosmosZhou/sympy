from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets, algebre


@apply
def apply(imply, index=None):
    eqs = axiom.is_Or(imply, copy=False)
    if index is None:
        return eqs
    return eqs[index]


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    f = Function.f(real=True, given=True)
    
    Eq << apply((f(y) > 0) | (f(x) > 0), index=0)
    
    Eq << ~Eq[0]
    
    Eq << algebre.et.imply.cond.apply(Eq[-1], index=0)
    
    Eq <<= Eq[-1] & Eq[1]
    

if __name__ == '__main__':
    prove(__file__)

