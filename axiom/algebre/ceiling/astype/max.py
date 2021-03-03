from sympy import *
from axiom.utility import prove, apply
import axiom

@apply
def apply(ceil):
    m = axiom.is_Ceiling(ceil)
    args = axiom.is_Max(m)
    args = [ceiling(arg) for arg in args]

    return Equality(ceil, Max(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(ceiling(Max(x, y)))
    
if __name__ == '__main__':
    prove(__file__)