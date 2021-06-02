from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piecewise.imply.ou import piecewise_to_ou
    assert given.is_Contains
    return piecewise_to_ou(given)


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)

    f = Function.f(etype=dtype.real * (k,))
    g = Function.g(etype=dtype.real * (k,))
    h = Function.h(etype=dtype.real * (k,))
    p = Symbol.p(real=True, shape=(k,), given=True)

    Eq << apply(Contains(p, Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))))

    Eq << sets.ou.imply.contains.piecewise.rhs.apply(Eq[1], wrt=p)


if __name__ == '__main__':
    run()

