from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piecewise.imply.ou import piecewise_to_ou
    assert given.is_Contains
    return piecewise_to_ou(given)


@prove
def prove(Eq):
    from axiom import sets

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(etype=dtype.real * (k,))
    Eq << apply(Contains(p, Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))))

    Eq << sets.ou.imply.contains.piecewise.rhs.apply(Eq[1], wrt=p)


if __name__ == '__main__':
    run()

