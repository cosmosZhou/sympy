from util import *



@apply(simplify=False)
def apply(given, index=None):
    fx, fy = given.of(Suffice)
    if index is None:
        cond = fx
    else:
        eqs = fx.of(And)
        cond = eqs[index]
        if isinstance(index, slice):
            cond = And(*cond)

    return Suffice(fx, cond & fy)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    A = Symbol.A(etype=dtype.integer)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Suffice(Equal(f[n], g[n]) & Contains(n, A), Equal(f[n + 1], g[n + 1])), index=0)

    Eq << Suffice(Equal(f[n], g[n]) & Contains(n, A), Equal(f[n], g[n]), plausible=True)

    Eq << algebra.suffice.suffice.imply.suffice.et.apply(Eq[0], Eq[-1], simplify=False)



if __name__ == '__main__':
    run()
from . import both_sided
