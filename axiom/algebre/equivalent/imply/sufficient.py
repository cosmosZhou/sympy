from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Equivalent
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise


@plausible
def apply(given):
    fn, fn1 = axiom.is_Equivalent(given)        
    return Sufficient(fn, fn1)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << Eq[0].astype(Equal)
    
#     Eq << algebre.sufficient.imply.forall.rewrite.apply(Eq[1], wrt=n)
    
    Eq << ForAll[n:Equal(Eq[2].lhs, 1)](Equal(Eq[2].rhs, 1), plausible=True)
    
    Eq << Eq[-1].subs(Eq[2].reversed)
    
    Eq << Eq[-1].this.limits[0][1].lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.function.lhs.astype(Piecewise)
    
    Eq << algebre.forall.imply.sufficient.apply(Eq[-1])

        
if __name__ == '__main__':
    prove(__file__)
