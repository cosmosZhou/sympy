from util import *


@apply
def apply(given, index=-1):
    cond, et = given.of(Suffice)
    eqs = et.of(And)
    if index is not None:
        first = And(*eqs[:index])
        second = And(*eqs[index:])
        return Suffice(cond, first), Suffice(cond, second)
    return tuple((Suffice(cond, eq) for eq in eqs))


@prove
def prove(Eq):
    from axiom import algebra

    n, x, y = Symbol(integer=True, nonnegative=True)
    f, g, h = Function(integer=True)
    Eq << apply(Suffice(x > y, (f(x) > g(y)) & (f(x) > h(y))))

    Eq << Eq[0].apply(algebra.suffice.given.ou)

    Eq << algebra.suffice.imply.ou.apply(Eq[1])

    Eq << algebra.suffice.imply.ou.apply(Eq[2])

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

from . import split
from . import st
