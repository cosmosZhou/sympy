from util import *
import axiom

from axiom.algebra.eq.simplify.terms.negative import simplify_negative_terms


@apply(given=None)
def apply(given):
    assert given.is_LessEqual
    return Equivalent(given, simplify_negative_terms(given))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    a = Symbol.a(real=True)
    
    b = Symbol.b(real=True)
    
    Eq << apply(LessEqual(x - a, y - b))
    
    Eq << Eq[-1].this.lhs + a
    
    Eq << Eq[-1].this.lhs + b
    
        
if __name__ == '__main__':
    run()
