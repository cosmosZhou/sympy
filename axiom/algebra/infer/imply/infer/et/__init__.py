from util import *


@apply(simplify=False)
def apply(given, index=None):
    fx, fy = given.of(Infer)
    if index is None:
        cond = fx
    else:
        eqs = fx.of(And)
        cond = eqs[index]
        if isinstance(index, slice):
            cond = And(*cond)

    return Infer(fx, cond & fy)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    A = Symbol(etype=dtype.integer)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Infer(Equal(f[n], g[n]) & Element(n, A), Equal(f[n + 1], g[n + 1])), index=0)

    Eq << Infer(Equal(f[n], g[n]) & Element(n, A), Equal(f[n], g[n]), plausible=True)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[0], Eq[-1], simplify=False)


if __name__ == '__main__':
    run()
from . import both_sided
# created on 2018-02-02
