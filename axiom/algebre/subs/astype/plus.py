from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    expr, old, new = axiom.is_Subs(self)    
    
    args = axiom.is_Plus(expr)
    
    return Equality(self, Plus(*[Subs(arg, old, new) for arg in args]))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    t = Symbol.t(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
     
    Eq << apply(Subs(f(x) + g(x), x, t))
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << Eq[-1].this.rhs.args[0].doit()
    
    Eq << Eq[-1].this.rhs.doit()

if __name__ == '__main__':
    prove(__file__)

