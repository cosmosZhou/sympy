from util import *


@apply
def apply(given):
    return piecewise_to_ou(Equal, given)


def piecewise_to_ou(cls, given):
    piecewise, sym = given.of(cls)
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise
        func = lambda x, y: cls(y, x)
    else:
        func = cls

    piecewise = piecewise.of(Piecewise)

    univeralSet = S.BooleanTrue
    args = []

    for expr, cond in piecewise:
        condition = cond & univeralSet

        if not cond:
            invert = condition.invert()
            univeralSet &= invert

        eq = condition & func(expr, sym).simplify()
        args.append(eq)

    return Or(*args)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Element(x, A))

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.args[0].apply(algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1), Eq[-1].this.args[0].apply(algebra.cond.cond.imply.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.eq_piece.imply.ou.two)

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)


if __name__ == '__main__':
    run()

from . import two
# created on 2018-01-07
# updated on 2018-01-07
