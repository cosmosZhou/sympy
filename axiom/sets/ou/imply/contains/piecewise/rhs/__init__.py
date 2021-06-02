from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Contains(wrt, Piecewise(*expr_cond_pair(Contains, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    f = Function.f(etype=dtype.real * (k,))
    g = Function.g(etype=dtype.real * (k,))
    h = Function.h(etype=dtype.real * (k,))

    y = Symbol.y(real=True, shape=(k,), given=True)

    Eq << apply(Contains(y, f(x)) & Contains(x, A) | Contains(y, g(x)) & Contains(x, B // A) | Contains(y, h(x)) & NotContains(x, A | B), wrt=y)

    Eq << Eq[0].this.args[1].args[0].apply(sets.contains.imply.et.split.complement, simplify=None)

    Eq << Eq[-1].this.args[2].args[0].apply(sets.notcontains.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotContains(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(sets.ou.imply.contains.piecewise.rhs.two, wrt=y)

    Eq << Eq[-1].apply(sets.ou.imply.contains.piecewise.rhs.two, wrt=y)


if __name__ == '__main__':
    run()

from . import two
