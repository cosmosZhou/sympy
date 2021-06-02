from util import *


def split(given, index):
    eqs = given.of(And)

    if isinstance(index, slice):
        start, stop = index.start, index.stop
        return And(*eqs[index]), And(*eqs[:start] + eqs[stop:])

    if index < 0:
        index += len(eqs)

    return eqs[index], And(*eqs[:index] + eqs[index + 1:])


@apply
def apply(given, index=0):
    return split(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)

    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)

    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)), index=Slice[1:3])

    Eq << Suffice(Eq[0], Eq[1], plausible=True)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Suffice(Eq[0], Eq[2], plausible=True)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

