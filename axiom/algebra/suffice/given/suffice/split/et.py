from util import *
import axiom



@apply
def apply(given):
    fx, et = given.of(Suffice)
    eqs = et.of(And)
    return tuple(Suffice(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Suffice(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2])))

    Eq << Eq[0].apply(algebra.suffice.given.ou)

    Eq << Eq[1].apply(algebra.suffice.imply.ou)

    Eq << Eq[2].apply(algebra.suffice.imply.ou)

    Eq <<= Eq[-2] & Eq[-1]

if __name__ == '__main__':
    run()
