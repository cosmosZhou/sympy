from util import *


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = given.of(Any)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    if domain is None:
        x = limit[0]
        limit = (x,)
    else:
        x, S = Tuple.as_setlimit(limit)
        assert S in domain
        limit = (x, domain)

    limits[i] = limit
    return Any(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Any[e:S - {t}](f(e) > 0), domain=S)

    Eq << algebra.any.given.ou.apply(Eq[-1], cond={t})

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()

