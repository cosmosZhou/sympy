from util import *


@apply
def apply(given, *limits):
    print('axiom must be employed at the top level!', __file__)
    for x, *ab in limits:
        assert given._has(x)
        if len(ab) == 1:
            domain = ab[0]
            if domain.is_set:
                assert domain in given.domain_defined(x)
            else:
                return
        else:
            return

    return Any(given, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(integer=True)
    A = Symbol.A(etype=dtype.integer, emptyset=False)

    assert A.is_integer
    assert not A.is_emptyset

    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, (e, A))

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (e, A))

    Eq << algebra.all.imply.any.apply(Eq[-1])


if __name__ == '__main__':
    run()

