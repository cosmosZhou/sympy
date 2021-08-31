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
        i = given.variables.index(wrt)

    limit = limits[i]

    assert domain is not None

    x, S = Tuple.as_setlimit(limit)
    assert S in domain
    limit = (x, domain)

    limits[i] = limit
    return All(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    A, B = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(All[e:A](f(e) > 0), domain=A | B)

    Eq << ~Eq[0]

    Eq << algebra.all.any.imply.any_et.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

