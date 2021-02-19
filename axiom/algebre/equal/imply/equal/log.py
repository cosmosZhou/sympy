from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, log
from sympy.core.function import Function
import axiom
from axiom import algebre


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
    assert lhs.is_nonzero
    assert rhs.is_nonzero
        
    return Equality(log(lhs), log(rhs))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(Equality(f(x), g(x)))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    prove(__file__)


