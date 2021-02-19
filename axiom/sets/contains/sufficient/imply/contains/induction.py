from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, Boole

from sympy.core.numbers import oo
from sympy import ForAll
from sympy import LAMBDA
import axiom
from axiom import algebre, sets
from sympy.sets.contains import Contains
from sympy.core.symbol import dtype
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.sympify import sympify
from sympy.logic.boolalg import Sufficient


@apply
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    axiom.is_Contains(f0)
    
    fn, fn1 = axiom.is_Sufficient(sufficient)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() == start
    
    return fn




@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(etype=dtype.integer, shape=(oo,))
    
    Eq << apply(Contains(f[0], g[0]), Sufficient(Contains(f[n], g[n]), Contains(f[n + 1], g[n + 1])), n=n)
    
    h = Symbol.h(definition=LAMBDA[n](Boole(Contains(f[n], g[n]))))
    
    Eq << h[0].this.definition
    
    Eq << sets.contains.imply.equal.bool.contains.apply(Eq[0])
    
    Eq.equality = Eq[-1] + Eq[-2]
    
    Eq.sufficient = Sufficient(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.astype(Piecewise)
    
    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.equality, Eq.sufficient, n=n)

    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

        
if __name__ == '__main__':
    prove(__file__)
