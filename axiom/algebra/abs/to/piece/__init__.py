from util import *


@apply
def apply(self):
    x = self.of(Abs)
    assert x.is_extended_real
    return Equal(self, Piecewise((x, x >= 0), (-x, True)))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(abs(x))


if __name__ == '__main__':
    run()


from . import gt_zero
from . import is_zero
from . import lt_zero
from . import le_zero
# created on 2018-01-01
# updated on 2018-01-01
