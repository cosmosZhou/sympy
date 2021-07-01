from util import *



@apply(simplify=False)
def apply(given):
    fx, fy = given.of(Suffice)
    return Suffice(fx, fx & fy)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Suffice(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << algebra.suffice.imply.suffice.split.et.apply(Eq[1], index=0)



if __name__ == '__main__':
    run()
