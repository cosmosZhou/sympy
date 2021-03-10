from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    min_xy, z = axiom.is_Plus(self)
    if z.is_Min:
        min_xy, z = z, min_xy
    
    args = [e + z for e in axiom.is_Min(min_xy)]
    
    return Equality(self, Min(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    Eq << apply(Min(x, y) - z)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

    
if __name__ == '__main__':
    prove(__file__)
