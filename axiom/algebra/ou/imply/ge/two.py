from util import *
from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair



@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    return GreaterEqual(Piecewise(*expr_cond_pair(GreaterEqual, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)

    p = Symbol.p(real=True, shape=(k,), given=True)

    Eq << apply(GreaterEqual(f(x), p) & Contains(x, A) | GreaterEqual(g(x), p) & NotContains(x, A), wrt=p)

    Eq << Eq[1].apply(algebra.cond.given.et.ou, cond=Contains(x, A))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.cond.cond.imply.et, invert=True, swap=True), Eq[-1].apply(algebra.cond.cond.imply.et, swap=True)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << algebra.et.imply.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()

