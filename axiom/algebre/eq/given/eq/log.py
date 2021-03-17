from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(imply):
    lhs, rhs = axiom.is_Equal(imply)
    assert lhs.is_nonzero or rhs.is_nonzero
    
    return Equality(log(lhs), log(rhs))

@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(Equality(f(x), g(x)))
    
    Eq << Eq[1].apply(algebre.eq.imply.eq.exp)
    
if __name__ == '__main__':
    prove(__file__)


