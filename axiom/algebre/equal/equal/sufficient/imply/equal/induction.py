from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll
from sympy import LAMBDA
import axiom
from axiom import algebre
from sympy.core.sympify import sympify
from sympy.logic.boolalg import Sufficient


@apply(imply=True)
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, f1, sufficient = given
    axiom.is_Equal(f0)
    axiom.is_Equal(f1)
    fn, fn2 = axiom.is_Sufficient(sufficient)    
    assert fn._subs(n, n + 2) == fn2

    assert fn._subs(n, start) == f0
    assert fn._subs(n, start + 1) == f1
    assert n.domain.min() == start
    
    return fn




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equal(f[1], g[1]), Equal(f[2], g[2]), Sufficient(Equal(f[n], g[n]), Equal(f[n + 2], g[n + 2])), n=n, start=1)
    
    m = Symbol.m(integer=True, nonnegative=True)
    h = Symbol.h(definition=LAMBDA[m](f[2 * m + 1] - g[2 * m + 1]))
    
    Eq << h[0].this.definition
    
    Eq.is_zero = Eq[-1].this.rhs.subs(Eq[0])
    
    Eq.sufficient = Sufficient(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.reversed
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.reversed
    
    Eq << Eq[2].subs(n, 2 * m + 1)
    
    Eq << algebre.is_zero.sufficient.imply.is_zero.induction.apply(Eq.is_zero, Eq.sufficient, n=m)

    Eq << Eq[-1].this.lhs.definition
    
    Eq.odd = Eq[-1].reversed

    h = Symbol("h'", definition=LAMBDA[m](f[2 * m + 2] - g[2 * m + 2]))
    
    Eq << h[0].this.definition
    
    Eq.is_zero_even = Eq[-1].this.rhs.subs(Eq[1])
    
    Eq.sufficient_even = Sufficient(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)
    
    Eq << Eq.sufficient_even.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.reversed
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.reversed
    
    Eq << Eq[2].subs(n, 2 * m + 2)
    
    Eq << algebre.is_zero.sufficient.imply.is_zero.induction.apply(Eq.is_zero_even, Eq.sufficient_even, n=m)

    Eq << Eq[-1].this.lhs.definition
    
    Eq.even = Eq[-1].reversed
    
    Eq << algebre.equal.imply.forall_equal.limit_is_odd.apply(Eq.odd, m)
    
    Eq << algebre.equal.imply.forall_equal.limit_is_even.apply(Eq.even, m)
    
    Eq << Eq[-1].limits_subs(m, m - 2)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << algebre.forall.imply.forall.limits_swap.apply(Eq[-1])
    
    Eq << Eq[-1].subs(m, n)
    
        
if __name__ == '__main__':
    prove(__file__)
