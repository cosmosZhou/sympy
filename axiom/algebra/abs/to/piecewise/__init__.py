from util import *
import axiom



@apply
def apply(self):
    x = self.of(Abs)    
    return Equal(self, Piecewise((x, x >= 0), (-x, True)))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(abs(x))

    
if __name__ == '__main__':
    run()
    
from . import is_positive
from . import is_zero
