from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair
    or_eqs = given.of(Or)

    return GreaterEqual(Piecewise(*expr_cond_pair(GreaterEqual, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)

    p = Symbol.p(shape=(k,), real=True, given=True)

    Eq << apply(GreaterEqual(f(x), p) & Contains(x, A) | GreaterEqual(g(x), p) & Contains(x, B // A) | GreaterEqual(h(x), p) & NotContains(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(sets.contains.imply.et.split.complement, simplify=None)

    Eq << Eq[-1].this.args[2].args[1].apply(sets.notcontains.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotContains(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.ou.imply.ge.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.ge.two, wrt=p)


if __name__ == '__main__':
    run()

from . import two
