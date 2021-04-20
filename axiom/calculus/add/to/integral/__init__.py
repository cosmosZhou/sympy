from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, calculus
from axiom.algebra.add.to.sum import piece_together

@apply
def apply(self):
    assert self.is_Add

    return Equal(self, piece_together(Integral, self))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Integral[x:a:b](f(x)) + Integral[x:a:b](g(x)))
    return
    Eq << Eq[0].this.rhs.apply(calculus.integral.to.add)
    
    
if __name__ == '__main__':
    prove()
    
del limits
from . import limits
