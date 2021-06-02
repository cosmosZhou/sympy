from util import *



@apply
def apply(given, limit):
    assert given.is_NotContains

    k, a, b = limit
    e, A = given.args

    assert Range(a, b) in A.domain_defined(k)

    return NotContains(e, Cup[k:a:b](A))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(positive=True, integer=True, given=False)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotContains(x, A[k]), (k, 0, n))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq[0].subs(k, 0)

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq[0].subs(k, n)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq.induct.induct()

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

