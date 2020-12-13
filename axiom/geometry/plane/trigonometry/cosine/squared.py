from axiom.utility import plausible
from sympy.core.relational import Equality, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Unequal

from sympy import Symbol

from sympy import cos, pi, sin
from sympy.sets.sets import Interval, EmptySet
from sympy import Exists
from axiom import algebre, sets
from sympy.core.symbol import dtype

@plausible
def apply(x):    
    return Equality(cos(x) ** 2, 1 - sin(x) ** 2)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
        
    Eq << apply(x)
    
    Eq << Eq[-1] - Eq[-1].rhs.args[1]
    
    Eq << Eq[-1].this.lhs.trigsimp()
    
    
# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    prove(__file__)
