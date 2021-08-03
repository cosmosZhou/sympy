from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    return Less(Piecewise(*expr_cond_pair(Less, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    p = Symbol.p(real=True, shape=(k,), given=True)
    Eq << apply(Less(f(x), p) & Contains(x, A) | Less(g(x), p) & NotContains(x, A), wrt=p)

    Eq << Eq[1].apply(algebra.cond.given.et.ou, cond=Contains(x, A))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.et.imply.et.invoke, algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1), Eq[-1].apply(algebra.et.imply.et.invoke, algebra.cond.cond.imply.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << algebra.et.imply.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()

