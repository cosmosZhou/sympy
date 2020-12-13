from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo, Zero
from sympy import ForAll, LAMBDA
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Sufficient


@plausible
def apply(given, n=None):
    fn, fn1 = axiom.is_Sufficient(given)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, Zero())
    assert n.domain.min().is_zero
    
    return fn


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = LAMBDA[n](Piecewise((f[0], Equal(n, 0)), (h[n], True)))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), n=n)
    
    g = Symbol.g(definition=LAMBDA[n](Piecewise((f[0], Equal(n, 0)), (h[n], True))))
    Eq.equality = g[0].this.definition.reversed
    
    Eq.sufficient = Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << algebre.equality.sufficient.imply.equality.induction.apply(Eq.equality, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.rhs.definition
    
        
if __name__ == '__main__':
    prove(__file__)
