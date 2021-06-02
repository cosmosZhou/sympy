from util import *


@apply
def apply(self):
    zx, zy = self.of(Mul)
    z, x = zx.of(Basic - Basic)
    _z, y = zy.of(Basic - Basic)
    assert _z == z
    return Equal(self, ((z - x) ** 2 + (z - y) ** 2 - (x - y) ** 2) / 2)


@prove
def prove(Eq):
    
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    z = Symbol.z(complex=True)
    
    Eq << apply((z - x) * (z - y))
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    
if __name__ == '__main__':
    run()
