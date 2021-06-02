from util import *

import axiom


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(self, swap=False):
    x, y = self.of(Min)
    
    if swap:
        x, y = y, x
        
    return Equal(self, y - relu(-x + y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Min(x, y))
    
    Eq << Eq[0].this.rhs.args[1].args[1].defun()
    
    Eq << Eq[-1].this.rhs.args[1].astype(Min)
    
    Eq << Eq[-1].this.rhs.astype(Min)


if __name__ == '__main__':
    run()
