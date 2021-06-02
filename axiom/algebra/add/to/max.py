from util import *
import axiom



@apply
def apply(self):
    min_xy, z = self.of(Add)
    if z.is_Max:
        min_xy, z = z, min_xy
    
    args = [e + z for e in min_xy.of(Max)]
    
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
    run()
