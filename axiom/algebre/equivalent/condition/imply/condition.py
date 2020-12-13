from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Equivalent
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise
from sympy.functions.special.tensor_functions import Boole


@plausible
def apply(*given):
    equivalent, condition = given
    fn, fn1 = axiom.is_Equivalent(equivalent)        
    return condition._subs(fn, fn1)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(f[n] > 0, g[n] > 0), ForAll[n:f[n] > 0](h[n] > 0))
    
    Eq << Eq[0].astype(Equal)
    
    Eq << ForAll[n:Equal(Boole(f[n] > 0), 1)](h[n] > 0, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.limits[0][1].subs(Eq[-2])
    
    Eq << Eq[-1].this.limits[0][1].lhs.astype(Piecewise)

        
if __name__ == '__main__':
    prove(__file__)
