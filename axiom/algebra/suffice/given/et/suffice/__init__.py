from util import *


@apply
def apply(given, index=-1):
    fx, et = given.of(Suffice)
    eqs = et.of(And)
    first = And(*eqs[:index])
    second = And(*eqs[index:])
    
    return Suffice(fx, first), Suffice(fx, second)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    Eq << apply(Suffice(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2])))

    Eq << Eq[0].apply(algebra.suffice.given.ou)

    

    Eq << algebra.suffice.imply.ou.apply(Eq[1])

    Eq << algebra.suffice.imply.ou.apply(Eq[2])

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

from . import split
