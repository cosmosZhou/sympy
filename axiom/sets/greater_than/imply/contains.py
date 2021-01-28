from sympy.core.relational import GreaterThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from sympy.sets.contains import Contains
from axiom import algebre, sets
import axiom
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
# given: |A| >= 1
# A != {}


@apply(imply=True)
def apply(given):
    n, b = axiom.is_GreaterThan(given)

    return Contains(n, Interval(b, oo, integer=n.is_integer))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    Eq << apply(n >= b)
    
    Eq << Eq[-1].split()
    

if __name__ == '__main__':
    prove(__file__)

