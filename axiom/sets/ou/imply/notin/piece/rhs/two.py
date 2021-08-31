from util import *




@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    assert len(or_eqs) == 2
    return NotElement(wrt, Piecewise(*expr_cond_pair(NotElement, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A, S = Symbol(etype=dtype.real * k, given=True)
    f, g = Function(etype=dtype.real * (k,))
    Eq << apply(NotElement(y, f(x)) & Element(x, A) | NotElement(y, g(x)) & NotElement(x, A), wrt=y)

    Eq << Eq[1].apply(algebra.cond.given.et.ou, cond=Element(x, A))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].this.apply(algebra.cond.cond.imply.cond.subs, invert=True, ret=0), Eq[-1].this.apply(algebra.cond.cond.imply.cond.subs, ret=0)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << algebra.et.imply.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()