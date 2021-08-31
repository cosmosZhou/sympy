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


from . import is_positive
from . import is_zero
from . import is_nonpositive
from . import is_negative