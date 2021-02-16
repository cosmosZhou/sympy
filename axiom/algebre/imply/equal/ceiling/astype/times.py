from sympy import *
from axiom.utility import prove, apply
import axiom

@apply(imply=True)
def apply(ceil):
    x = axiom.is_Ceiling(ceil)

    return Equality(ceil, -floor(-x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x))
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.args[1].definition
    
if __name__ == '__main__':
    prove(__file__)