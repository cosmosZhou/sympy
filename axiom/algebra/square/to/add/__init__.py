from util import *


@apply
def apply(self): 
    x, y = self.of(Add ** 2)
    return Equal(self, x * x + 2 * x * y + y * y)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply((x + y) ** 2)
    
    Eq << Eq[-1].this.lhs.expand()

    
if __name__ == '__main__':
    run()

from . import st
