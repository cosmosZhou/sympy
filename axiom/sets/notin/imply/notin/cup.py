from util import *


@apply
def apply(given, limit):
    assert given.is_NotElement

    k, a, b = limit
    e, A = given.args

    assert Range(a, b) in A.domain_defined(k)

    return NotElement(e, Cup[k:a:b](A))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(positive=True, integer=True, given=False)
    x, k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotElement(x, A[k]), (k, 0, n))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq[0].subs(k, 0)

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq[0].subs(k, n)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Suffice(Eq[1], Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

