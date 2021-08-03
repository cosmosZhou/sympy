from util import *

from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)

    assert len(or_eqs) == 2
    return Contains(wrt, Piecewise(*expr_cond_pair(Contains, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(etype=dtype.real * (k,))
    g = Function.g(etype=dtype.real * (k,))
    S = Symbol.S(etype=dtype.real * k, given=True)
    Eq << apply(Contains(y, f(x)) & Contains(x, A) | Contains(y, g(x)) & NotContains(x, A), wrt=y)

    Eq << Eq[1].apply(algebra.cond.given.et.ou, cond=Contains(x, A))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].this.apply(algebra.et.imply.et.invoke, algebra.cond.cond.imply.cond.subs, invert=True), Eq[-1].this.apply(algebra.et.imply.et.invoke, algebra.cond.cond.imply.cond.subs)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << algebra.et.imply.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()

