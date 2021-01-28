from sympy import *
from axiom.utility import prove, apply
import axiom


@apply(imply=True)
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(x) / x, g(x) / x), x, 0)
    
    Eq << Eq[1].subs(Eq[0])    


if __name__ == '__main__':
    prove(__file__)

