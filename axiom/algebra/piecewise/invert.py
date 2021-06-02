from util import *


@apply
def apply(piecewise, index=0):
    [*ec] = piecewise.of(Piecewise)

    _, cond = ec[index]

    expr_next, cond_next = ec[index + 1]
    cond_next &= cond.invert()

    ec[index + 1] = (expr_next, cond_next)
    if ec[-1][1]:
        ...
    else:
        ec[-1][1] = True

    return Equal(piecewise, piecewise.func(*ec))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    g = Function.g(shape=(), real=True)
    f = Function.f(shape=(), real=True)
    h = Function.h(shape=(), real=True)

    Eq << apply(Piecewise((g(x), Contains(x, A)), (f(x), NotContains(x, B)), (h(x), True)))

    p = Symbol.p(Eq[0].lhs)
    Eq << p.this.definition

    Eq << algebra.eq_piecewise.imply.ou.apply(Eq[-1])

    Eq << algebra.ou.imply.eq.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.front)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

