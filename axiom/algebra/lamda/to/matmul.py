from util import *
import axiom

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(lamda):
    function, *limits = lamda.of(Lamda)

    j, zero, k_1 = axiom.limit_is_Interval(limits, integer=True)
    assert zero.is_Zero
    k = k_1

    lhs, rhs = function.of(MatMul)
    assert not lhs._has(j)

    base, _j = rhs.of(Indexed)
    m, n = base.shape
    assert k <= m

    assert rhs._has(j)

    if j != _j:
        h = _j - j
        assert not h._has(j)
        return Equal(lamda, lhs @ base[h:k + h].T)
    return Equal(lamda, lhs @ base[:k].T)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)

    k = Symbol.k(domain=Range(1, m + 1))
    Q = Symbol.Q(shape=(n,), real=True)
    K = Symbol.K(shape=(m, n), real=True)
    a = Symbol.a(real=True, shape=(oo,))

    Eq << apply(Lamda[j:k](Q @ K[j]))

    j = Symbol.j(domain=Range(0, k))

    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], j)


if __name__ == '__main__':
    run()

