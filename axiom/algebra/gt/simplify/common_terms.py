from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from axiom.algebra.eq.simplify.terms.common import simplify_common_terms


@apply(given=None)
def apply(given):
    assert given.is_Greater    
    return Equivalent(given, simplify_common_terms(given))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    a = Symbol.a(real=True)
    
    Eq << apply(Greater(x + a, y + a))
    
    Eq << Eq[-1].this.lhs - a
    
        
if __name__ == '__main__':
    prove()
