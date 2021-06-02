from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert given.is_Exists

    if isinstance(cond, Boolean):
        if wrt is None:
            wrt = cond.wrt

        cond = wrt.domain_conditioned(cond)

    return given.split(cond, wrt=wrt)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    f = Function.f(integer=True, shape=())
    d = Symbol.d(real=True, positive=True, given=True)
    Eq << apply(Exists[x:-d:d](f(x) > 0), cond=x > 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.all.all.imply.all.limits_union)

    Eq << ~Eq[-1]

if __name__ == '__main__':
    run()

