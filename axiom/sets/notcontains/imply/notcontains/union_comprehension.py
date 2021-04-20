from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(given, limit):
    assert given.is_NotContains    
    
    k, a, b = limit
    e, A = given.args
    
    assert Interval(a, b, right_open=True, integer=True) in A.domain_defined(k)
    
    return NotContains(e, UNION[k:a:b](A))


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True, given=False)
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
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=1)    

    
if __name__ == '__main__':
    prove()

