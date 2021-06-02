from util import *
import axiom



@apply
def apply(given):
    fx, et = given.of(Suffice)
    eqs = et.of(And)
    return And(*(Suffice(fx, eq) for eq in eqs))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Suffice(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2])))

    Eq << Eq[0].apply(algebra.suffice.given.ou)

    Eq << algebra.ou.given.et.apply(Eq[-1])

    Eq << Eq[1].this.args[0].apply(algebra.suffice.imply.ou)

    Eq << Eq[-1].this.args[1].apply(algebra.suffice.imply.ou)



if __name__ == '__main__':
    run()
