from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equal(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(x), g(x)), (x, -oo, oo))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], Integral[x:-oo:oo], simplify=False)    


if __name__ == '__main__':
    prove()

