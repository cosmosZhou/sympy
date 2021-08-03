from util import *


def split(given, index):
    eqs = given.of(And)

    if isinstance(index, slice):
        start, stop = index.start, index.stop
        return And(*eqs[index]), And(*eqs[:start] + eqs[stop:])

    return And(*eqs[:index]), And(*eqs[index:])


@apply
def apply(given, index=-1):
    first, second = split(given, index)
    return first, second


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)), index=slice(1, 3))

    Eq << Suffice(Eq[0], Eq[1], plausible=True)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Suffice(Eq[0], Eq[2], plausible=True)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()


from . import delete
from . import subs
del collect
from . import collect
from . import invoke
