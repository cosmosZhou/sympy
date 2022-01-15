from util import *


def split(given, index):
    eqs = given.of(And)

    if isinstance(index, slice):
        start, stop = index.start, index.stop
        return And(*eqs[index]), And(*eqs[:start] + eqs[stop:])
    elif index is None:
        return eqs
    
    return And(*eqs[:index]), And(*eqs[index:])


@apply
def apply(given, index=-1):
    return split(given, index)    


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)), index=slice(1, 3))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Infer(Eq[0], Eq[2], plausible=True)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    
    


if __name__ == '__main__':
    run()


from . import delete
from . import subs
from . import collect
# created on 2018-01-04
# updated on 2021-11-20