from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equal(ArgMax(lhs, *limits).simplify(), ArgMax(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], ArgMax[i:n], simplify=False)    

if __name__ == '__main__':
    prove()

from . import definition