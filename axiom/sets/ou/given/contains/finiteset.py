from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    or_eqs = axiom.is_Or(given)
    
    common_term = None
    for eq in or_eqs:
        x, y = axiom.is_Equal(eq)
        if common_term is None:
            common_term = {x, y}
        else:
            common_term &= {x, y}
    if len(common_term) == 1:
        x, *_ = common_term
        
        rhs = set()
        for eq in or_eqs: 
            s = {*eq.args}
            s.remove(x)
            rhs |= s
            
        return Contains(x, FiniteSet(*rhs))            


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True, given=True)
    
    Eq << apply(Equal(x, a) | Equal(x, b) | Equal(x, c))
    
    Eq << sets.contains.imply.ou.split.finiteset.apply(Eq[-1])
    
        
if __name__ == '__main__':
    prove()

