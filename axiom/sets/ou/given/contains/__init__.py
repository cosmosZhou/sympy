from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    or_eqs = axiom.is_Or(given)

    ss = []    
    var = None
    for eq in or_eqs:
        x, s = axiom.is_Contains(eq)
        
        if var is None:
            var = x
        else:
            assert x == var
        ss.append(s)
        
    return Contains(x, Union(*ss))            


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    C = Symbol.C(etype=dtype.real)
    
    Eq << apply(Or(Contains(x, A), Contains(x, B), Contains(x, C)))
    
    Eq << sets.contains.imply.ou.split.union.apply(Eq[1], simplify=False)
    
        
if __name__ == '__main__':
    prove()

from . import finiteset
