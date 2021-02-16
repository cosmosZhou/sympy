from sympy import *
from axiom.utility import prove, apply
from axiom import algebre

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(x, negate=False):
    if negate:
        x = -x
    return LessThan(x, abs(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
     
    Eq << apply(x)
    
    Eq << Eq[-1].bisect(x > 0).split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq << Eq[-1].apply(algebre.strict_greater_than.less_than.imply.strict_less_than.transit)
    
    Eq << Eq[-2].this.args[0].apply(algebre.is_positive.imply.equal.abs)
    
    Eq << Eq[-1].apply(algebre.strict_greater_than.equal.imply.strict_greater_than.transit)    

    
if __name__ == '__main__':
    prove(__file__)

