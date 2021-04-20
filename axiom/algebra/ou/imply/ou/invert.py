from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given, pivot=0):
    or_eqs = axiom.is_Or(given)
    
    precondition = or_eqs[pivot]
    del or_eqs[pivot]
    statement = Or(*or_eqs)
    
    return Or(precondition, precondition.invert() & statement)            


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)), pivot=1)
    
    Eq << algebra.ou.given.et.apply(Eq[-1])


if __name__ == '__main__':
    prove()

