from util import *


@apply
def apply(given, index=-1):
    from axiom.algebra.et.imply.et import split
    first, second = split(given, index)
    return first, second


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)))

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()


from . import split
del collect
from . import collect
del mul
from . import mul
from . import subs
from . import transit
