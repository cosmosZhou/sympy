from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, old, new):
    assert self.is_Derivative
    assert self._has(new)
    return Equal(self, Subs(self._subs(new, old), old, new))

    
@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    t = Symbol.t(real=True)
    Eq << apply(Derivative(f(t), t), x, t)
    
    Eq << Eq[-1].this.rhs.doit()

    
if __name__ == '__main__':
    prove()
