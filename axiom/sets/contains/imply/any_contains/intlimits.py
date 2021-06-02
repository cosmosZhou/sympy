from util import *


@apply
def apply(given, *limits):
    assert given.is_Contains

    for limit in limits:
        limit = Tuple.as_setlimit(limit)
        var, *domain = limit
        assert given._has(var)
        if domain:
            domain = domain[0]
            assert domain in given.domain_defined(var)

    return Exists(given, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(positive=True, integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Contains(x, A[k]), (k, 0, n))

    Eq << ~Eq[-1]

    Eq << algebra.cond.all.imply.all_et.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

