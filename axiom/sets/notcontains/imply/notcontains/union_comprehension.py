from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.numbers import oo
from sympy import UNION
from sympy.sets.sets import Interval
from axiom import algebre


@apply(imply=True)
def apply(given, limit):
    assert given.is_NotContains    
    
    k, a, b = limit
    e, A = given.args
    
    assert Interval(a, b, right_open=True, integer=True) in A.domain_defined(k)
    
    return NotContains(e, UNION[k:a:b](A))




@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotContains(x, A[k]), (k, 0, n))
    
    Eq.initial = Eq[-1].subs(n, 1)
    
    Eq << Eq[0].subs(k, 0)
    
    Eq.induction = Eq[1].subs(n, n + 1)
    
    Eq << Eq[0].subs(k, n)
    
    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq.induction.induct()
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq.initial, Eq[-1], n=n, start=1)    
    
if __name__ == '__main__':
    prove(__file__)

