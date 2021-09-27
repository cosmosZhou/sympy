from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Necessary)
    return Suffice(fn1, fn)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed


if __name__ == '__main__':
    run()
from . import reverse
