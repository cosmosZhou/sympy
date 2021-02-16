from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True, simplify=False)
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equality(rhs, lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Equality(x, y))
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

