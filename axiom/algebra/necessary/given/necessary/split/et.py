from util import *



@apply
def apply(given):
    et, fx = given.of(Necessary)
    eqs = et.of(And)
    return tuple(Necessary(eq, fx) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Necessary(Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2]), Equal(f[n], g[n])))

    Eq << Eq[0].reversed

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-1])

    Eq << Eq[-2].reversed

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()
