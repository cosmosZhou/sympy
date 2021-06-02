from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Unequal(Piecewise(*expr_cond_pair(Unequal, or_eqs, wrt, reverse=True)).simplify(), wrt)


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

    Eq << apply(Unequal(f(x), p) & Contains(x, A) | Unequal(p, g(x)) & Contains(x, B // A) | Unequal(p, h(x)) & NotContains(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(sets.contains.imply.et.split.complement, simplify=None)

    Eq << Eq[-1].this.args[2].args[1].apply(sets.notcontains.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotContains(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.ou.imply.ne.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.ne.two, wrt=p)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

from . import two
