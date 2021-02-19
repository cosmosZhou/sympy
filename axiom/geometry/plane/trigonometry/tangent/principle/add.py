from sympy import sin, cos, tan
from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Unequal

from sympy import Symbol

from sympy import cos, pi
from sympy.sets.sets import Interval, EmptySet
from sympy import Exists
from axiom import algebre, sets, geometry
from sympy.core.symbol import dtype
from sympy.core.numbers import Pi
from sympy.core.mul import Times


@apply
def apply(x, y):
    return Equality(tan(x + y), (tan(x) + tan(y)) / (1 - tan(x) * tan(y)))        


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
        
    Eq << apply(x, y)
    
    Eq << Eq[0].this.lhs.astype(Times)
    
    Eq << tan(x).this.astype(Times)
    
    Eq << tan(y).this.astype(Times)
    
    Eq << Eq[1].subs(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.rhs.ratsimp()
    
    Eq << geometry.plane.trigonometry.sine.principle.add.apply(x, y)
    
    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x, y)
    
    Eq << Eq[-3].subs(Eq[-1], Eq[-2])


if __name__ == '__main__':
    prove(__file__)
