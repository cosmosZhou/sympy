
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
from sympy.core.relational import Unequal
from sympy.sets.contains import Contains


@apply(imply=True)
def apply(given):
    assert given.is_Exists
    assert len(given.limits) == 1
    x, S = given.limits[0]
    return Unequal(S, x.emptySet)




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:S](f(e) > 0))
    
    Eq << Exists[e:S](Contains(e, S) & Eq[0].function, plausible=True)
    
    Eq << Eq[-1].simplify()
    Eq << Eq[-1].split()    

    
if __name__ == '__main__':
    prove(__file__)

