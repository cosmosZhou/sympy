from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given, q=None):
    mod, r = axiom.is_Equal(given)
    n, d = axiom.is_Mod(mod)
    if q is None:
        q = Symbol.q(integer=True)
        
    return Exists[q](Equal(n, q * d + r))


@prove
def prove(Eq):
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)
    
    d = Symbol.d(integer=True, given=True)
    
    r = Symbol.r(integer=True)
    
    Eq << apply(Equal(n % d, r))
    
    Eq << Eq[0].this.lhs.definition
    
    Eq << Eq[-1] + n // d * d
    
    q = Eq[1].variable
    
    Eq << algebre.exists.given.exists.subs.apply(Eq[1], q, n // d)
    
if __name__ == '__main__':
    prove(__file__)
