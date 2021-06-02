from util import *
import axiom



@apply
def apply(lamda):
    function, *limits = lamda.of(Lamda)

    (i, zero, n_1), (j, _zero, _n_1) = axiom.limits_are_Interval(limits, integer=True)
    assert zero.is_Zero and _zero.is_Zero
    assert n_1 == _n_1

    n = n_1

    lhs, rhs = function.of(Mul)
    if lhs.is_KroneckerDelta:
        lhs, rhs = rhs, lhs

    _i, _j = rhs.of(KroneckerDelta)
    assert i == _i and j == _j or i == _j and j == _i

    if lhs._has(j):
        assert not lhs._has(i)
        return Equal(lamda, Identity(n) * Lamda[j:n](lhs).simplify())
    elif lhs._has(i):
        assert not lhs._has(j)
        return Equal(lamda, Identity(n) * Lamda[i:n](lhs).simplify())


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

