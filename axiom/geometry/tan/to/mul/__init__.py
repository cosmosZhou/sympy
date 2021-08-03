from util import *


@apply
def apply(self): 
    x = self.of(Tan)
    
    rhs = sin(x) / cos(x)
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(tan(x))


if __name__ == '__main__':
    run()

from . import principle
