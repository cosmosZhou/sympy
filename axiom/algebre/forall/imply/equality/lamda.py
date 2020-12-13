from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol, ForAll
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict


@plausible
def apply(given):
    function, *limits = axiom.is_ForAll(given)
    axiom.is_Equal(function)
    
    dic = limits_dict(limits)
    assert len(dic) == 1
    (x, domain), *_ = dic.items()
    assert domain.is_integer and domain.is_Interval
    
    return function.reference((x, domain))

from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    
    Eq << apply(ForAll[i:n](Equality(f(i), g(i))))
    
    Eq << Eq[0].reference((i,0,n-1))
    

if __name__ == '__main__':
    prove(__file__)

