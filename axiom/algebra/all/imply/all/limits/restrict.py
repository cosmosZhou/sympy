from util import *


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = given.of(All)

    if isinstance(domain, tuple):
        wrt, *domain = domain
        if len(domain) == 1:
            domain = domain[0]

    if wrt is None:
        i = 0
    else:
        try:
            i = given.variables.index(wrt)
        except ValueError:
            limits.append((wrt,))
            i = -1

    limit = limits[i]

    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
    else:
        x, S = Tuple.as_setlimit(limit)

    assert domain in S
    limit = (x, domain)

    limits[i] = limit
    return All(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.real, given=True)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True, given=True)
    f = Function.f(shape=(), integer=True)
    Eq << apply(All[e:S](f(e) > 0), domain=S - {t})

    Eq << ~Eq[-1]

    Eq << algebra.all.any.imply.any_et.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
