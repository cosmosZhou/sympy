from util import *


@apply
def apply(lamda):
    (expr, (_i, _j)), (i, n), (j, _n) = lamda.of(Lamda[Mul[Expr, KroneckerDelta], Tuple[0, Expr], Tuple[0, Expr]])

    assert n == _n    
    assert i == _i and j == _j or i == _j and j == _i

    if expr._has(j):
        assert not expr._has(i)
        return Equal(lamda, Identity(n) * Lamda[j:n](expr).simplify())
    elif expr._has(i):
        assert not expr._has(j)
        return Equal(lamda, Identity(n) * Lamda[i:n](expr).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(oo,))
    Eq << apply(Lamda[j:n, i:n](a[j] * KroneckerDelta(i, j)))

    i = Symbol.i(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
