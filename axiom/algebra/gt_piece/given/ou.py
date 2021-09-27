from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piece.imply.ou import piecewise_to_ou
    return piecewise_to_ou(Greater, given)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(p > Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True)))

    Eq << Eq[1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << algebra.ou.imply.lt.apply(Eq[-1], p).reversed


if __name__ == '__main__':
    run()
