from util import *


@apply
def apply(given):
    assert given.is_Equal

    return piecewise_to_ou(given)


def piecewise_to_ou(given):
    piecewise, sym = given.args
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise

    (e0, c0), (e1, _) = piecewise.of(Piecewise)

    univeralSet = S.true

    condition = c0 & univeralSet

    invert = condition.invert()
    univeralSet &= invert

    cond0 = condition & given.func(sym, e0).simplify()

    cond1 = univeralSet & given.func(sym, e1).simplify()

    return Or(cond0, cond1)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)

    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)

    p = Symbol.p(real=True, shape=(k,), given=True)

    Eq << apply(Equal(p, Piecewise((f(x), Contains(x, A)), (g(x), True))))

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Contains(x, A))

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.args[0].apply(algebra.cond.cond.imply.et, invert=True, swap=True), Eq[-1].this.args[0].apply(algebra.cond.cond.imply.et, swap=True)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)


if __name__ == '__main__':
    run()

