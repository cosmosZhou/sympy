from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import INTERSECTION
from sympy.sets.sets import Interval


@plausible
def apply(given, limit):
    assert given.is_Contains    
    
    k, a, b = limit
    e, A = given.args
    
    assert Interval(a, b, integer=True) in A.domain_defined(k)
    
    return Contains(e, INTERSECTION[k:a:b](A), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(domain=[1, oo], integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(Contains(x, A[k]), (k, 0, n - 1))
    
    Eq << Eq[-1].subs(n, 1)
    
    Eq << Eq[0].subs(k, 0)
    
    Eq << Eq[1].subs(n, n + 1)
    
    Eq << Eq[0].subs(k, n)
    
    Eq <<= Eq[-1] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

