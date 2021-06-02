from util import *


@apply
def apply(self):
    import axiom
    x2, y2 = axiom.is_Subtract(self)
    x = x2.of(Basic ** 2)
    y = y2.of(Basic ** 2)
    return Equal(self, (x - y) * (x + y))


@prove
def prove(Eq):
    
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    
    Eq << apply(x * x - y * y)
    
    Eq << Eq[0].this.rhs.expand()
    
    
if __name__ == '__main__':
    run()
