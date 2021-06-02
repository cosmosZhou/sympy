
from util import *

import axiom

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(lamda):
    function, *limits = lamda.of(Lamda)

    (i, zero, n_1), (j, _zero, _n_1) = axiom.limits_are_Interval(limits, integer=True)
    assert zero.is_Zero and _zero.is_Zero

    _i, _j = function.of(KroneckerDelta)
    assert i == _i and j == _j or i == _j and j == _i

    assert n_1 == _n_1

    n = n_1

    return Equal(lamda, Identity(n))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(Lamda[j:n, i:n](KroneckerDelta(i, j)))

    i = Symbol.i(domain=Range(0, n))

    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()

