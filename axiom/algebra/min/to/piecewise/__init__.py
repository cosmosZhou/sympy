from util import *


@apply
def apply(self):
    arg, *args = self.of(Min)
    this = self.func(*args)
    rhs = Piecewise((arg, arg <= this), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Min(x, y))


if __name__ == '__main__':
    run()
from . import lt

from . import gt

from . import ge
