from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given, k=None):
    n = axiom.is_even(given)
    if k is None:
        k = Symbol.k(integer=True)
        
    return Exists[k](Equal(n, k * 2))


@prove
def prove(Eq):
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)
    
    r = Symbol.r(integer=True)
    
    Eq << apply(Equal(n % 2, 0))
    
    k = Eq[1].variable
    
    Eq << algebre.equal.imply.exists.definition.mod.apply(Eq[0], q=k)
    
    
if __name__ == '__main__':
    prove(__file__)
