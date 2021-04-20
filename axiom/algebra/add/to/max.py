from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    min_xy, z = axiom.is_Add(self)
    if z.is_Max:
        min_xy, z = z, min_xy
    
    args = [e + z for e in axiom.is_Max(min_xy)]
    
    return Equal(self, Max(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    Eq << apply(Max(x, y) - z)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Add)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

    
if __name__ == '__main__':
    prove()
