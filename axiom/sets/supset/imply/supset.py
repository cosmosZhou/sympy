from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.concrete.expr_with_limits import UNION
from sympy.sets.contains import Supset
from sympy.core.numbers import oo


@plausible
def apply(given, *limits):
    assert given.is_Supset
    A, fx = given.args
    
    return Supset(A, UNION(fx, *limits).simplify(), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)
   
    Eq << apply(Supset(A, x[i]), (i, 0, m - 1))
    
    Eq << Eq[-1].subs(m, 1)
    
    Eq << Eq[0].subs(i, 0)
    
    Eq << Eq[1].subs(m, m + 1)
        
    Eq << Eq[0].subs(i, m)
    
    Eq <<= Eq[-1] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

