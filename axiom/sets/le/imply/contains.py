from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given: |A| >= 1
# A != {}


@apply
def apply(given):
    n, b = axiom.is_LessThan(given)

    return Contains(n, Interval(-oo, b, integer=n.is_integer))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    Eq << apply(n <= b)
    
    Eq << Eq[-1].simplify()
    

if __name__ == '__main__':
    prove(__file__)

