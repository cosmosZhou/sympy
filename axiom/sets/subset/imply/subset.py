from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import UNION
from sympy.sets.contains import Subset
from sympy.core.numbers import oo
from axiom import algebre


@plausible
def apply(given, *limits):
    assert given.is_Subset
    fx, A = given.args
    
    return Subset(UNION(fx, *limits).simplify(), A)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)
   
    Eq << apply(Subset(x[i], A), (i, 0, m - 1))
    
    Eq.initial = Eq[-1].subs(m, 1)
    
    Eq << Eq[0].subs(i, 0)
    
    Eq.induction = Eq[1].subs(m, m + 1)
        
    Eq << Eq[0].subs(i, m)
    
    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq.induction.induct(imply=True)
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq.initial, Eq[-1], n=m, start=1, simplify=None)    
    
if __name__ == '__main__':
    prove(__file__)

