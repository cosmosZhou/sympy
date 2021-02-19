from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(minimize):
    function, *limits = axiom.is_Minimize(minimize)
    return ForAll(LessThan(minimize, function), *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True)
    N = Symbol.N(integer=True)
    
    Eq << apply(Minimize[n:N + 1](abs(x[n])))
        
#     Eq << ~Eq[-1]
    
    _n = Symbol.n(domain=Interval(0, N, integer=True))
    Eq << Eq[-1].limits_subs(n, _n)
    
    Eq << Eq[-1].this.lhs.limits_subs(n, _n)
    
#     Eq << Eq[-1].simplify()

    
if __name__ == '__main__':
    prove(__file__)

