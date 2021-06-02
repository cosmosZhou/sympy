from util import *


import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    expr, old, new = self.of(Subs)    
    
    args = expr.of(Add)
    
    return Equal(self, Add(*[Subs(arg, old, new) for arg in args]))


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
    run()

