from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(imply):
    lhs, rhs = axiom.is_Equal(imply)
    assert lhs.is_nonzero or rhs.is_nonzero
    
    return Equal(log(lhs), log(rhs))

@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)
    
    Eq << apply(Equal(f(x), g(x)))
    
    Eq << Eq[1].apply(algebra.eq.imply.eq.exp)
    
if __name__ == '__main__':
    prove()


