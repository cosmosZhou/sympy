from sympy import Symbol, Bool, Or
from sympy.core.relational import Equal, LessEqual
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
from axiom import algebra, sets
import axiom
from sympy.core.numbers import Number
from sympy.core.mul import Mul
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessEqual(abs(x), abs(x - y) + abs(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
     
    Eq << apply(x, y)
    
    Eq << algebra.imply.le.abs.add.apply(x - y, y)

    
if __name__ == '__main__':
    prove()

