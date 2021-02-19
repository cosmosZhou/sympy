from sympy import Symbol, Boole, Or
from sympy.core.relational import Equality, LessThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
from axiom import algebre, sets
import axiom
from sympy.core.numbers import Number
from sympy.core.mul import Times
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessThan(abs(x), abs(x - y) + abs(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
     
    Eq << apply(x, y)
    
    Eq << algebre.imply.less_than.abs.add.apply(x - y, y)

    
if __name__ == '__main__':
    prove(__file__)

