from util import *


@apply
def apply(x, evaluate=False):
    return LessEqual(x, Ceiling(x), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.imply.ge.ceiling.apply(x)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

from . import integer
from . import upper_bound
# created on 2018-10-28
# updated on 2018-10-28
