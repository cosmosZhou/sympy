from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import algebre


@apply(imply=True)
def apply(given):
    xy = axiom.is_nonpositive(given)
    x, y = axiom.is_Times(xy)
    return Or(And(x >= 0, y <= 0), And(x <= 0, y >= 0)) 


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(x * y <= 0)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].this.args[0].apply(algebre.ou.imply.ou.invert, pivot=1)
    
    Eq << Eq[-1].this.args[1].apply(algebre.ou.imply.ou.invert, pivot=1)
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[1].astype(Or)
    
    Eq << Eq[-1].this.args[-1].apply(algebre.is_positive.is_positive.imply.is_positive)
    
    Eq << algebre.condition.condition.imply.condition.apply(Eq[0], Eq[-1], invert=True)
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].apply(algebre.is_negative.is_negative.imply.is_positive)
    
    Eq <<= Eq[-1] & Eq[0]
    
    
if __name__ == '__main__':
    prove(__file__)
