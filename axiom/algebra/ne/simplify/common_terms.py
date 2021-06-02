from util import *
import axiom

from axiom.algebra.eq.simplify.terms.common import simplify_common_terms


@apply(given=None)
def apply(given):
    assert given.is_Unequal    
    return Equivalent(given, simplify_common_terms(given))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    
    a = Symbol.a(real=True, shape=(n,))
    
    Eq << apply(Unequal(x + a, y + a))
    
    Eq << Eq[-1].this.lhs - a
    
        
if __name__ == '__main__':
    run()
