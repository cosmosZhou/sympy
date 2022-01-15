from util import *


@apply
def apply(given):
    assert given.is_LessEqual
    from axiom.algebra.eq_piece.imply.ou.two import piecewise_to_ou
    return piecewise_to_ou(given)

@prove
def prove(Eq):
    from axiom import algebra

    x, p = Symbol(real=True, shape=(), given=True)
    A = Symbol(etype=dtype.real, given=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(p <= Piecewise((f(x), Element(x, A)), (g(x), True)))

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Element(x, A))

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.args[0].apply(algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1), Eq[-1].this.args[0].apply(algebra.cond.cond.imply.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    

    


if __name__ == '__main__':
    run()
# created on 2019-12-03
# updated on 2022-01-08
