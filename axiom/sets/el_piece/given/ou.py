from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piece.imply.ou import piecewise_to_ou
    return piecewise_to_ou(Element, given)


@prove
def prove(Eq):
    from axiom import sets

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(etype=dtype.real * (k,))
    Eq << apply(Element(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << sets.ou.imply.el.piece.rhs.apply(Eq[1], wrt=p)


if __name__ == '__main__':
    run()

# created on 2018-09-24
