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


@apply
def apply(x, y):
    return Equal(cos(x - y), cos(x) * cos(y) + sin(x) * sin(y))        


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
        
    Eq << apply(x, y)
    
    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x, -y)
    
# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    prove()
