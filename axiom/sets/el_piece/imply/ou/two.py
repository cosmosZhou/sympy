from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piece.imply.ou.two import piecewise_to_ou
    assert given.is_Element
    return piecewise_to_ou(given)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real * k, given=True)
    f, g = Function(etype=dtype.real * (k,))
    Eq << apply(Element(p, Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Element(x, A))

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.args[0].apply(algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1), Eq[-1].this.args[0].apply(algebra.cond.cond.imply.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)


if __name__ == '__main__':
    run()

# created on 2018-09-21
# updated on 2018-09-21
