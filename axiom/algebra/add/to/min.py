from util import *


@apply
def apply(self):
    min_xy, z = self.of(Add)
    if z.is_Min:
        min_xy, z = z, min_xy
    
    args = [e + z for e in min_xy.of(Min)]
    
    return Equal(self, Min(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    Eq << apply(Min(x, y) - z)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Add)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

    
if __name__ == '__main__':
    run()
