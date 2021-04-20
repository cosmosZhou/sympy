from sympy import sin, cos
from axiom.utility import prove, apply
from sympy.core.relational import Equal, Less, Greater, \
    LessEqual, GreaterEqual, Unequal

from sympy import Symbol

from sympy import cos, pi
from sympy.sets.sets import Interval, EmptySet
from sympy import Exists
from axiom import algebra, sets, geometry
from sympy.core.symbol import dtype
from sympy.core.numbers import Pi


@apply
def apply(x, y):
    return Equal(sin(x + y), sin(x) * cos(y) + cos(x) * sin(y))        


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
        
    Eq << apply(x, y)
    
    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x + Pi() / 2, y)
    
    Eq << -Eq[-1]


if __name__ == '__main__':
    prove()
