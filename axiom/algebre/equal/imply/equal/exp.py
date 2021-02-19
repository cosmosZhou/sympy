from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equality(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(i), g(i)))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], exp)


if __name__ == '__main__':
    prove(__file__)

