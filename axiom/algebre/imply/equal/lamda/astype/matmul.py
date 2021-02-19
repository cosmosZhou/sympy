from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(lamda):
    function, *limits = axiom.is_LAMBDA(lamda)
    
    j, zero, k_1 = axiom.limit_is_Interval(limits, integer=True)
    assert zero.is_Zero
    k = k_1
    
    lhs, rhs = axiom.is_MatMul(function)
    assert not lhs._has(j)

    base, _j = axiom.is_Indexed(rhs)
    m, n = base.shape
    assert k <= m
    
    assert rhs._has(j)
    
    if j != _j:
        h = _j - j
        assert not h._has(j)    
        return Equality(lamda, lhs @ base[h:k + h].T)
    return Equality(lamda, lhs @ base[:k].T)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    k = Symbol.k(domain=Interval(1, m, integer=True))
    Q = Symbol.Q(shape=(n,), real=True)
    K = Symbol.K(shape=(m, n), real=True)
    a = Symbol.a(real=True, shape=(oo,))
    
    Eq << apply(LAMBDA[j:k](Q @ K[j]))
    
    j = Symbol.j(domain=Interval(0, k - 1, integer=True))
    
    Eq << algebre.equal.given.equal.getitem.apply(Eq[0], j)


if __name__ == '__main__':
    prove(__file__)

