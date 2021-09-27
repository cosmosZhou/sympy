from util import *


@apply
def apply(given, *limits):
    assert given.is_Element

    for limit in limits:
        limit = Tuple.as_setlimit(limit)
        var, *domain = limit
        assert given._has(var)
        if domain:
            domain = domain[0]
            assert domain in given.domain_defined(var)

    return Any(given, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Element(x, A[k]), (k, 0, n))

    Eq << ~Eq[-1]

    Eq << algebra.cond.all.imply.all_et.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

