from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert given.is_Any

    if isinstance(cond, Boolean):
        if wrt is None:
            wrt = cond.wrt

        cond = wrt.domain_conditioned(cond)

    from axiom.algebra.sum.to.add.split import split
    return split(Any, given, cond, wrt=wrt)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    f = Function.f(integer=True)
    d = Symbol.d(real=True, positive=True, given=True)
    Eq << apply(Any[x:-d:d](f(x) > 0), cond=x > 0)

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.args[0].apply(algebra.all.imply.et.split, cond=x > 0)


if __name__ == '__main__':
    run()

