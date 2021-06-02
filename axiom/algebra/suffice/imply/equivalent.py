from util import *
import axiom



@apply
def apply(given):
    fx, fy = given.of(Suffice)
    return Equivalent(fx, fx & fy)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))

    Eq << apply(Suffice(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq.suffice, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[1])

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[0])



if __name__ == '__main__':
    run()

